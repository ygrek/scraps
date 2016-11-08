# Inspect OCaml heap and values in GDB
# 2016/01/17
#
# https://github.com/ygrek/scraps/blob/master/mlvalues.py
# (c) 2011 ygrek
# (c) 2016 Amplidata, a HGST company.
#
# Licensed under the terms of BSD 3-clause
#
# Description
# -----------
#
# You will need GDB with python support (>=7.0?).
# This code reimplements Std.dump from extlib and is
# limited to information available in runtime representation
# of OCaml values. Not complete, doesn't handle cycles at all,
# tested only on x64.
#
# At GDB prompt input:
#    source mlvalues.py
#
# And inspect any OCaml value:
#    ml_dump [/r[N]] <value> # address or symbol representing OCaml value
# optional /r flag controls the recursion depth limit when printing (default 1).
# e.g.:
#    ml_dump caml_globals
#    ml_dump /r &camlList
#
# Or inspect an array of values:
#    ml_dump [/r[N]] <start address> <number of values>
# e.g.:
#    ml_dump <value*> 1 # inspecting single pointer to value
#    ml_dump gray_vals 5
#
# Inspect local (stack) GC roots:
#    ml_dump [/r[N]] local_roots
#
# Show OCaml heap information:
#    ml_heap
#
# Scan OCaml heap region:
#    ml_scan [/r[N]] addr bytes
#
# Use Python class directly for detailed scrutiny, e.g.:
#    python x = OCamlValue(gdb.parse_and_eval("caml_globals")); print x.size_words()
#
# Changelog
# ---------
#
# 2016-01-17
#   New command `ml_scan` to show values in OCaml heap
#
# 2015-10-22
#   Truncate long strings when printing
#
# 2014-04-29
#   Limit recursion depth when printing
#
# 2014-03-31
#   Be precise with type when reading runtime variables
#
# 2013-08-25
#   Use `cast` instead of `reinterpet_cast` for better compatibility (by ADEpt)
#   Better handling of missing debuginfo in OCaml runtime
#   Add usage examples
#
# 2013-08-01
#   Dump local (stack) GC roots with `ml_dump local_roots`
#
# 2012-08-09
#   Fix printing of strings with binary data (use 'latin1' codec)
#
# 2012-04-11
#   Dump the array of OCaml values with ml_dump
#   Inspect closure blocks
#   Tweak formatting
#
# 2012-03-07
#   New command `ml_heap` - shows some general information about OCaml heap:
#     * GC parameters
#     * total heap size
#     * allocated chunks layout
#
# 2011-12-27
#   Show symbol and name for custom values
#   Catch gdb.MemoryError and continue printing
#   Correctly lookup types
#
# 2011-12-24
#   Initial

import functools
import traceback
import collections
import bisect
import struct
import ctypes
from enum import Enum

def TraceMemoryError(f):
  """
  Attribute that wraps the function in order to display a traceback
  when accessing invalid memory
  """
  def wrapper(*args, **kwargs):
    try:
      return f(*args, **kwargs)
    except gdb.MemoryError as me:
      print("Function %s attempted to access invalid memory" % f.__name__)
      traceback.print_exc()
      raise
  return functools.update_wrapper(wrapper, f)

def TraceAll(f):
  """
  Attribute that wraps the function in order to display a traceback
  """
  def wrapper(*args, **kwargs):
    try:
      return f(*args, **kwargs)
    except:
      traceback.print_exc()
      raise
  return functools.update_wrapper(wrapper, f)

def try_dereference(gdbval):
  """
  Attempt to dereference a gdb.Value returning None when the access fails.
  """
  try:
    ret = gdbval.dereference()
    ret.fetch_lazy()
    return ret
  except gdb.MemoryError:
    return None

# gdb.Type's used often throughout the script
intnat = size_t = charp = doublep = heap_chunk_head_p = caml_contextp = caml_thread_structp = None

# do not lookup types at class level cause this script may be run before
# the inferior image is loaded and gdb can't know sizeof(long) in advance
def init_types():
  global intnat, size_t, charp, doublep, heap_chunk_head_p, caml_contextp, caml_thread_structp

  if doublep is not None:
    return

  try:
    heap_chunk_head_p = gdb.lookup_type("heap_chunk_head").pointer()
  except:
    print("Didn't find 'heap_chunk_head'. Major heap walking is unavailable")
    pass

  try:
    caml_contextp = gdb.lookup_type("struct caml_context").pointer()
  except:
    print("Didn't find 'struct caml_context'. Stack walking unavailable.")
    pass

  try:
    caml_thread_structp = gdb.lookup_type("caml_thread_struct").pointer()
  except:
    print("Didn't find 'caml_thread_struct'. System thread roots unavailable.")
    pass

  intnat = gdb.lookup_type("intnat")
  size_t = gdb.lookup_type("size_t")
  charp = gdb.lookup_type("char").pointer()
  doublep = gdb.lookup_type("double").pointer()
  # keep this one last

class MemoryType(Enum):
  """
  Various types of memory we're interested in
  """
  General = 0
  Stack = 1
  MajorHeap = 2
  MinorHeap = 3
  Code = 4
  StaticData = 5
  OtherStatic = 6
  Finalisers = 7
  GC_Metadata = 8
  LinuxSpecial = 9
  Unknown = 10

  Address = 100

  @classmethod
  def all(cls):
    return [ cls.General, cls.Stack, cls.MajorHeap, cls.MinorHeap, cls.Code, cls.StaticData, cls.OtherStatic, cls.Finalisers, cls.GC_Metadata, cls.LinuxSpecial, cls.Unknown]

@functools.total_ordering
class MemoryRange:
  """
  A range of memory inside the process' memory address space
  """
  def __init__(self, address, size, source, description, memtype=None):
    """
    Args:
      address, size: describe memory range
      source: where this memory range was defined (e.g. a file, coredump or gdb)
      description: describes the contents of this memory range
      memtype: a MemoryType parameter if the contents are known
               or None otherwise. In this case this class will attempt
               to deduce the MemoryType from the description, following
               some standard gdb names
    """
    # We might be passed gdb.Value's, so convert them to native int's to reduce memory footprint
    self.startaddr = int(address)
    self.size = int(size)
    self.source = source
    self.description = description
    if memtype is None:
      self.memtype = MemoryRange._determine_memtype(description)
    else:
      self.memtype = memtype

  @staticmethod
  def _determine_memtype(description):
    """
    Determine the type of memory from the description
    This function knows most of the descriptions returned by 'info target' and 'info proc mappings'
    and will deduce the actual memory type based on that.
    """
    if description.startswith('.'):
      t = description.split()[0]
      if t in [ ".data", ".bss", ".rodata" ]:
        return MemoryType.StaticData
      elif t == ".text":
        return MemoryType.Code
      else:
        return MemoryType.OtherStatic
    elif description.startswith('['):
      if description == "[stack]":
        return MemoryType.Stack
      elif description in [ "[vdso]", "[vsyscall]", "[vvar]" ]:
        return MemoryType.LinuxSpecial
      elif description == "[heap]":
        return MemoryType.General
      else:
        return MemoryType.Unknown
    elif description.startswith("load"):
      return MemoryType.General
    elif "libc" in description:
      # C library is known to have some odd-named sections
      return MemoryType.OtherStatic
    elif description == "text_env":
      return MemoryType.OtherStatic
    else:
      return MemoryType.Unknown

  @staticmethod
  def from_addr(address):
    """Create a single-address MemoryRange"""
    return MemoryRange(address, size_t.sizeof, "MemorySpace.from_addr", "address", MemoryType.Address)

  @staticmethod
  def part_of(other, start, size):
    """Create a MemoryRange that spans a chunk of the provided MemoryRange"""
    return MemoryRange(start, size, other.source, other.description, other.memtype)

  @property
  def lastaddr(self):
    """Last valid address in this range"""
    return self.startaddr + self.size - 1

  @property
  def endaddr(self):
    """Post-end address of this range"""
    return self.startaddr + self.size

  def __contains__(self, address):
    return self.startaddr <= address < self.endaddr

  def _overlaps(self, other):
    return self.startaddr <= other.startaddr < self.endaddr \
        or other.startaddr <= self.startaddr < self.endaddr

  def __eq__(self, other):
    return isinstance(other, MemoryRange) and self.startaddr == other.startaddr

  def __lt__(self, other):
    return isinstance(other, MemoryRange) and self.startaddr < other.startaddr

  def settype(self, memtype, description=None):
    """
    Override the memory type and, optionally, the description
    """
    self.memtype = memtype
    if description is not None:
      self.description = description

  def __str__(self):
    return "0x%08X - 0x%08X is %15s|%s" % (self.startaddr, self.startaddr + self.size, self.memtype.name, self.description)


class MemorySpace:
  """Describes the inferior process' memory address space/layout"""
  def __init__(self):
    self.have_accurate_info = True
    self.populate_ranges()
    self.annotate_stacks()
    self.annotate_major_heap()
    self.annotate_minor_heap()
    self.annotate_finalisers()

  def set_inaccurate(self, missing):
    print("Some debug information is missing from the binary: %s . Not all functionality is available" % missing)
    self.have_accurate_info = False

  def display(self, verbosity):
    """
    Pretty print the memory address space with varying verbosity levels:
      0: only OCaml Stack and Minor/Major Heap areas are displayed
      1: In addition, static data, code and known GC metadata areas are displayed
      2: all memory types are displayed
    """
    if verbosity == 0:
      interesting = [ MemoryType.Stack, MemoryType.MinorHeap, MemoryType.MajorHeap ]
    elif verbosity == 1:
      interesting = [ MemoryType.Stack, MemoryType.MinorHeap, MemoryType.MajorHeap,
                      MemoryType.StaticData, MemoryType.Code, MemoryType.GC_Metadata ]
    else:
      interesting = MemoryType.all()

    for r in self.ranges:
      if r.memtype in interesting:
        print("%s" % str(r))

  def get_range(self, address):
    """Get the memory range containing the provided address or None otherwise."""
    index = bisect.bisect(self.ranges, MemoryRange.from_addr(address))
    if index >= len(self.ranges):
      return None
    memrange = self.ranges[index-1]
    if address in memrange:
      return memrange
    return None

  def is_address_of_type(self, address, *memtypes):
    """Return True of the address is contained in a memory range of one of the provided types"""
    memrange = self.get_range(address)
    return memrange is not None and memrange.memtype in memtypes

  def is_on_stack(self, address):
    """Indicate whether the address is on one of the inferior threads' stack"""
    return self.is_address_of_type(address, MemoryType.Stack)

  def is_in_heap(self, address):
    """Indicate whether the address points to data in the OCaml heap"""
    return self.is_address_of_type(address, MemoryType.MajorHeap, MemoryType.MinorHeap)

  # Beware, on some architectures data is sometimes stored intermingled with code in the .text section
  # Typically this is after the return instruction from a function
  def is_valid_data(self, address):
    """Indicate whether the address points to a memory range known to contain data"""
    return self.is_address_of_type(address,
                                   MemoryType.MajorHeap, MemoryType.MinorHeap,
                                   MemoryType.StaticData, MemoryType.Stack,
                                   MemoryType.Finalisers)

  def is_code(self, address):
    """Indicate whether the address points to a memory range containing code"""
    return self.is_address_of_type(address, MemoryType.Code)

  def search_memory_of_types(self, pattern, *memtypes):
    """Search all memory of the given types for the provided pattern.
       The pattern must adhere to the buffer interface, the simplest
       way to create this is probably struct.pack(...)."""
    inferior = gdb.selected_inferior()
    locations = []
    for memrange in self.ranges:
      if memrange.memtype not in memtypes:
        continue

      loc = ctypes.c_void_p(memrange.startaddr).value
      end = ctypes.c_void_p(memrange.endaddr).value
      while loc < end:
        loc = inferior.search_memory(loc, end - loc, pattern)
        if loc is None or loc == 0:
          loc = end
        else:
          locations.append(loc)
          loc += size_t.sizeof

    return locations

  # TODO: make this function truncate the existing ranges, rather than delete them
  # It will allow annotate_split_range to keep return value over multiple splits
  def split_range_at(self, address):
    """Split a memory range at the provided address and returns both new ranges."""
    index = bisect.bisect(self.ranges, MemoryRange.from_addr(address))
    index -= 1
    # address is before any existing ranges
    if index < 0:
      return None, None

    memrange = self.ranges[index]
    # address points to the beginning of an existing range
    if memrange.startaddr == address:
      previous = None if index == 0 else self.ranges[index-1]
      return previous, memrange

    # address inside the memory range
    if address in memrange:
      first = MemoryRange(memrange.startaddr, address - memrange.startaddr, memrange.source, memrange.description, memrange.memtype)
      second = MemoryRange(address, memrange.startaddr + memrange.size - address, memrange.source, memrange.description, memrange.memtype)

      del self.ranges[index]
      bisect.insort(self.ranges, first)
      bisect.insort(self.ranges, second)
      return first, second

    # address (right) after the memory range and not contained by another memory range
    previous = memrange if address == memrange.endaddr else None
    return previous, None

  def tentative_add_range(self, memrange):
    """Add a memory range, leaving any existing overlaps untouched, yet filling holes where necessary"""
    # optimize the easy case. makes rest of code simpler
    if not len(self.ranges):
      bisect.insort(self.ranges, memrange)
      return

    probeaddr = memrange.startaddr
    while probeaddr < memrange.endaddr:
      index = bisect.bisect(self.ranges, MemoryRange.from_addr(probeaddr))

      # before first
      if index == 0:
        nxt = self.ranges[index]
        lastaddr = nxt.startaddr
        bisect.insort(self.ranges, MemoryRange.part_of(memrange, probeaddr, lastaddr - probeaddr))
        probeaddr = nxt.endaddr
        continue

      # after last
      if index >= len(self.ranges):
        prev = self.ranges[index-1]
        startaddr = prev.endaddr
        if startaddr <= probeaddr:
          bisect.insort(self.ranges, MemoryRange.part_of(memrange, probeaddr, memrange.endaddr - probeaddr))
          probeaddr = memrange.endaddr
        else:
          probeaddr = startaddr
        continue

      # in between 2
      prev = self.ranges[index-1]
      if probeaddr in prev:
        probeaddr = prev.endaddr
        continue

      nxt = self.ranges[index]
      if nxt.startaddr in memrange:
        bisect.insort(self.ranges, MemoryRange.part_of(memrange, probeaddr, nxt.startaddr - probeaddr))
        probeaddr = nxt.endaddr
      else:
        bisect.insort(self.ranges, MemoryRange.part_of(memrange, probeaddr, memrange.endaddr - probeaddr))
        probeaddr = memrange.endaddr

  def annotate_split_range(self, address, size, memtype, description):
    """Annotate an existing range (or part thereof) as the specified MemoryType, splitting the range where necessary"""
    _, _ = self.split_range_at(address) # do not keep return values, following call may delete it from self.ranges
    end, _ = self.split_range_at(address+size)
    begin = self.get_range(address)

    begin.settype(memtype, description)
    if end != begin:
      print("Annotating '%s' over 2 separate ranges: %s and %s" % (description, str(begin), str(end)))
      # TODO: merge the two
      end.settype(memtype, description)

  def populate_ranges(self,):
    """Populate the memory ranges from coredump info or live gdb information"""
    self.ranges = list()
    # coredump: info target shows all sections in full detail
    # live debug: only file-backed sections are shown
    targetinfo = gdb.execute("info target", False, True)
    for line in targetinfo.splitlines():
      line = line.strip()
      if line.startswith('`'):
        line = line.split("'")[1]
        source = line[1:]
        continue
      if not line.startswith("0x"):
        continue

      start, dash, end, str_is, memtype = line.split(maxsplit=4)
      assert(dash == '-' and str_is == 'is')
      start = int(start, 16)
      end = int(end, 16)
      new_range = MemoryRange(start, end-start, source, memtype)
      startoverlap = self.get_range(start)
      endoverlap = self.get_range(end)

      if endoverlap == startoverlap:
        endoverlap = None

      #TODO: splitup and punch holes/replace
      if memtype.startswith('.'):
        # gdb reports loadXXX sections on top of file-backed sections of the binary
        # probably because the kernel maps writeable pages on top of them
        # Therefore, keep the more accurate description from the file-backed section
        if startoverlap is not None and startoverlap.memtype == MemoryType.General:
          previous, current = self.split_range_at(start)
          self.ranges.remove(current)
          startoverlap = None
        if endoverlap is not None and endoverlap.memtype == MemoryType.General:
          current, end = self.split_range_at(end)
          self.ranges.remove(current)
          endoverlap = None

      if startoverlap is not None and endoverlap is not None:
        print("Overlapping memory ranges: %s in %s -> %s" %
            (new_range, str(startoverlap), str(endoverlap)))
      bisect.insort(self.ranges, new_range)

    # live target: run-time allocated memory and some file-backed sections
    # There typically is overlap with the 'info target' output, so give precedence
    # to the previously added ranges
    mappinginfo = gdb.execute("info proc mappings", False, True)
    for line in mappinginfo.splitlines():
      line = line.strip()
      if not line.startswith("0x"):
        continue

      items = line.split()
      if len(items) == 4:
        start, end, size, offset = items
        source = "unknown"
      elif len(items) == 5:
        start, end, size, offset, source = items
      else:
        print("Unexpected line when parsing 'info proc mappings': %s" % line)
        continue

      start = int(start, 16)
      size = int(size, 16)
      end = int(end, 16)

      new_range = MemoryRange(start, size, source, source)
      self.tentative_add_range(new_range)

  def annotate_stacks(self):
    """
    Mark all memoryranges containing thread stacks as such.
    We do this by taking the stack pointer of each thread
    and marking the target address' memory range.
    There typically are guard pages around stacks, they will
    not be marked as stack.
    """
    curthread = gdb.selected_thread()
    try:
      for thread in gdb.selected_inferior().threads():
        thread.switch()

        # This is different depending on gdb version
        try:
          frame = gdb.newest_frame()
          stackpointer = frame.read_register("sp")
        except:
          regname, as_hex, as_int = gdb.execute("info register sp", False, True).split()
          stackpointer = int(as_hex, 16)
        memrange = self.get_range(stackpointer)
        tid = thread.ptid[1] if thread.ptid[1] else thread.ptid[2]
        if memrange is None:
          print("Did not find stack of thread %d" % tid)
          continue
        memrange.settype(MemoryType.Stack, "Stack of thread %d(TID %d)" % (thread.num, tid))
    finally:
      curthread.switch()

  def annotate_major_heap(self):
    """
    Mark all memory ranges containing OCaml stack as such.
    Memory ranges are split when needed to avoid marking padding as actual heap.
    """
    # TODO: we could provide a fallback path by manually taking the proper bytes as
    # the ml_heap command does
    if heap_chunk_head_p is None:
      self.set_inaccurate("major heap info")
      return

    heap_chunk_ptr = gdb.parse_and_eval("caml_heap_start").cast(heap_chunk_head_p)
    try:
      while heap_chunk_ptr != 0:
        heap_chunk_head_ptr = heap_chunk_ptr - 1
        heap_chunk_head = heap_chunk_head_ptr.dereference()

        block = heap_chunk_head["block"]
        size = heap_chunk_head["size"]

        memrange = self.get_range(heap_chunk_head_ptr)
        if memrange is not None:
          self.annotate_split_range(heap_chunk_ptr.cast(size_t), size, MemoryType.MajorHeap, "Major heap")
        else:
          new_range = MemoryRange(heap_chunk_ptr.cast(size_t), size, "gdb", "Major Heap", MemoryType.MajorHeap)
          assert(false) # This shouldn't happen
          self.tentative_add_range(new_range)

        heap_chunk_ptr = heap_chunk_head["next"].cast(heap_chunk_head_p)
    except gdb.MemoryError:
      print("OCaml major heap linked list is corrupt: last entry = 0x%08X" % (heap_chunk_ptr.cast(size_t)))

    gray_vals = gdb.parse_and_eval("gray_vals").cast(size_t)
    gray_vals_cur = gdb.parse_and_eval("gray_vals_cur").cast(size_t)
    gray_vals_size = gdb.parse_and_eval("gray_vals_size").cast(size_t)
    gray_vals_end = gdb.parse_and_eval("gray_vals_end").cast(size_t)
    self.annotate_split_range(gray_vals, gray_vals_size, MemoryType.GC_Metadata, "major GC's gray values")
    self.annotate_split_range(gray_vals_cur, gray_vals_end - gray_vals_cur, MemoryType.GC_Metadata, "major GC's current gray values")

  def annotate_minor_heap(self):
    """
    Mark the minor heap memory range as such.
    """
    minor_start = gdb.parse_and_eval("caml_young_base").cast(size_t)
    minor_size = gdb.parse_and_eval("caml_young_end").cast(size_t) - minor_start

    memrange = self.get_range(minor_start)
    if memrange is not None:
      self.annotate_split_range(minor_start, minor_size, MemoryType.MinorHeap, "Minor heap")
    else:
      new_range = MemoryRange(minor_start, minor_size, "gdb", "Minor Heap", MemoryType.MinorHeap)
      self.set_inaccurate("minor heap memory map info")
      bisect.insort(self.ranges, new_range)

  def annotate_finalisers(self):
    """
    Mark the table of finalisers as such.
    """
    table = gdb.parse_and_eval("final_table").cast(size_t)
    try:
      size = gdb.parse_and_eval("'finalise.d.c'::size").cast(size_t)
    except gdb.error:
      try:
        size = gdb.parse_and_eval("'finalise.c'::size").cast(size_t)
      except:
        self.set_inaccurate("finalisers")
        return
    if table != 0 and size != 0:
      self.annotate_split_range(table, size, MemoryType.Finalisers, "Finalisers table")

memoryspace = None

def init_memoryspace(reload=False):
  """Load memory space information from the inferior process."""
  global memoryspace
  if memoryspace is not None and not reload:
    return

  try:
    memoryspace = MemorySpace()
  except:
    traceback.print_exc()
    raise

def resolve(address):
  """Resolve an address to a symbol (function/variable name)."""
  symbol = gdb.execute("info symbol 0x%08X" % address.cast(size_t), False, True).split(" ",1)[0]
  if symbol == "No": # FIXME "No symbol matches"
    return "0x%08X" % address.cast(size_t)
  else:
    return "%s" % symbol

# This class represents gdb.Value as OCaml value.
# Analogue to stdlib Obj module.
#
# It probably contains more casts than strictly necessary,
# but after all who am I to understand python type system?
# Just a mere OCaml coder. And this is my first python program.
class OCamlValue:

  VALUE_TAG = 0
  LAZY_TAG = 246
  CLOSURE_TAG = 247
  OBJECT_TAG = 248
  INFIX_TAG = 249
  FORWARD_TAG = 250
  NO_SCAN_TAG = 251
  ABSTRACT_TAG = 251
  STRING_TAG = 252
  DOUBLE_TAG = 253
  DOUBLE_ARRAY_TAG = 254
  CUSTOM_TAG = 255
  FINAL_TAG = 255
  INT_TAG = 1000
  OUT_OF_HEAP_TAG = 1001
  UNALIGNED_TAG = 1002

  VALID_TAGS = (VALUE_TAG, LAZY_TAG, CLOSURE_TAG, OBJECT_TAG, INFIX_TAG, FORWARD_TAG, NO_SCAN_TAG, ABSTRACT_TAG, STRING_TAG,
                DOUBLE_TAG, DOUBLE_ARRAY_TAG, CUSTOM_TAG)

  def __init__(self,v, parent=None, parentindex=None):
    if isinstance(v, OCamlValue):
      self.v = v.v
    elif not isinstance(v, gdb.Value):
      self.v = gdb.Value(v).cast(intnat)
    else:
      self.v = v.cast(intnat)
    self.parent = parent
    self.parentindex = parentindex
    if parent is not None and parentindex is None:
      raise Exception("If a parent is specified, the parentindex is also expected")

  def is_int(self):
    """Indicate whether the OCamlValue is an integer."""
    return self.v & 1 != 0

  def is_block(self):
    """Indicate whether the OCamlValue is a pointer to an OCaml block."""
    return self.v & 1 == 0

  @staticmethod
  def of_int(x):
    return OCamlValue(gdb.Value((x<<1) + 1))

  @staticmethod
  def of_val(x):
    assert(x & 1 == 0)
    return OCamlValue(gdb.Value(x))

  @staticmethod
  def of_bool(x):
    assert(x & (~1) == 0)
    return OCamlValue.of_int(x != 0)

  def int(self):
    """Get the integer value of this instance. Must only be called if it is an int."""
    assert(self.is_int())
    return self.v >> 1

  def val(self):
    """Get the gdb.Value of this instance."""
    return self.v

  def _string(self,enc='latin1'):
    assert self.tag() == OCamlValue.STRING_TAG

    byte_size = self.size_bytes()
    if byte_size is None:
      return "Invalid string: could not determine string size: value outside the heap: value = 0x%X" % self.v

    padsize_byte = (self.v + (byte_size - 1)).cast(charp)
    padsize = try_dereference(padsize_byte)
    if padsize is None:
      return "Invalid string: pad byte not in valid memory. value=0x%X, size in bytes=%d, pad byte: 0x%X" % (self.v, byte_size, padsize_byte)

    slen = byte_size - 1 - padsize
    trailing_nul = try_dereference((self.v + slen).cast(charp))
    assert(trailing_nul is not None) # we shouldn't get here if we could dereference padsize above
    if trailing_nul != 0:
      return "Invalid string: no NUL-byte at end of string. value=0x%X, size in bytes=%d, last byte=%d" % (self.v, byte_size, trailing_nul)

    if slen <= 1024:
        s = self.v.cast(charp).string(enc, 'ignore', slen)
        return s.__repr__()
    else:
        s = self.v.cast(charp).string(enc, 'ignore', 256)
        return "%s..<%d bytes total>" % (s.__repr__(), slen)

  def _float(self):
    assert self.tag() == OCamlValue.DOUBLE_TAG
    words = self.size_words()
    if words != doublep.target().sizeof: # Don't check for None, the assert already implies it
      return "Invalid float: size=%d" % words
    f = try_dereference(self.v.cast(doublep))
    assert(f is not None) # This is quite unlikely, unless v is outside the heap, while the header is inside
    return "%f" % f

  def __cmp__(self,other):
    if self.v == other.v:
      return 0
    else:
      if self.v > other.v:
        return 1
      else:
        return -1

  def __str__(self):
    if self.is_int():
      return ("%d" % self.int())
    else:
      return ("0x%X" % self.val())

  def __repr__(self):
    return "OCamlValue(%s)" % self.__str__()

  def hd(self):
    """Get the header value or None if inaccessible. Must only be called on a block."""
    header = (self.v - intnat.sizeof).cast(size_t.pointer())
    return try_dereference(header)

  def tag(self):
    """Get the block tag or None if inaccessible. Must only be called on a block."""
    if self.is_int():
      return OCamlValue.INT_TAG
    else:
      hd = self.hd()
      if hd is None:
        return OCamlValue.OUT_OF_HEAP_TAG
      return hd & 0xFF

  def _unsafe_field(self,i):
    """
    Get the contents of the indicated field or None if inaccessible.
    Does not check boundaries nor validate this is a block.
    """
    x = try_dereference( (self.v + (i * intnat.sizeof)).cast(intnat.pointer()) )
    if x is None:
      return None
    return OCamlValue(x, parent=self, parentindex = i)

  def field(self,i):
    """
    Get the contents of the indicated field or None if inaccessible.
    Must only be called on a block, cannot obtain a double from a double array.
    """
    assert self.is_block()
    assert self.tag () != OCamlValue.DOUBLE_ARRAY_TAG # FIXME not implemented
    n = self.size_words()
    if n is None:
      return None
    if i < 0 or i >= n:
      raise IndexError("field %d size %d" % (i,n))
    return self._unsafe_field(i)
    #t = intnat.array(n).pointer()
    #return OCamlValue(self.v.cast(t).dereference()[i])

  def fields(self):
    """
    Get a list of all fields of this block.
    Must only be called on a block, cannot obtain fields of a double array.
    When any access goes out of bounds, a single None value is appended to
    the list.
    """
    assert self.is_block()
    assert self.tag () != OCamlValue.DOUBLE_ARRAY_TAG # FIXME not implemented

    words = self.size_words()
    if words is None:
      return [None]

    a = []
    for i in range(int(words)):
      field = self._unsafe_field(i)
      a.append(field)
      if field is None:
        break # Append a single invalid value to indicate out-of-bounds to the user
    return a

  def size_words(self):
    """
    Return the size of this block in number of words or None if inaccessible
    Must only be called on a block.
    """
    assert self.is_block()
    hd = self.hd()
    if hd is None:
      return None
    return hd >> 10

  def size_bytes(self):
    """
    Return the size of this block in number of bytes or None if inaccessible
    Must only be called on a block.
    """
    size_words = self.size_words()
    if size_words is None:
      return None
    return size_words * intnat.sizeof

  def _is_list(self):
    """Indicate if this block describes a list."""
    # TODO
    if self.is_int():
      return self.int() == 0
    else:
      return self.size_words() == 2 and self.tag() == 0 and self.field(1)._is_list()

  def get_list(self):
    """Parse an OCaml list into a python list."""
    a = []
    l = self
    while l.is_block():
      a.append(l.field(0))
      l = l.field(1)
    return a

  def get_list_length(self):
    """Get the length of an OCaml list"""
    n = 0
    l = self
    while l.is_block():
      n+=1
      l = l.field(1)
    return n

  def resolve(self):
    """Resolve the block pointer contained in this OCamlValue."""
    return resolve(self.val())

  def show_opaque(self,s):
    print("<%s at 0x%x>" % (s,self.val()))

  def show_seq(self,seq,delim,recurse,raw=False):
    for i, x in enumerate(seq):
      if i:
        print(delim)
      if raw:
        print(x.resolve())
      else:
        x.show(recurse)

  # Verbosity:
  # Error information is always shown
  # 0: Print type of the OCamlValue
  # 1: Print type and value of the OCamlValue, only displays number of items for sequence types
  # 2: Print type and value of the OCamlValue, display full contents of not to long,
  #    otherwise same as 1
  # Each of the following functions interprets the OCamlValue per the function name
  # and displays the value according to the given verbosity.
  #
  # The functions get all of their input through function arguments
  # to avoid excessive fetching through gdb.Value and duplicating parsing logic.

  def _stringify_int(self, value, verbosity):
    if verbosity == 0:
      return "Integer"
    else:
      return "Integer(%d/0x%08X)" % (value, value)

  def _stringify_invalid_block(self, pointer, reason, verbosity):
    if verbosity == 0:
      return "Invalid block(%s)" % reason
    else:
      return "Invalid block(%s, v=0x%08X)" % (reason, pointer)

  def _stringify_invalid_size(self, pointer, size, item, verbosity):
    if verbosity == 0:
      return "Invalid size %s"
    else:
      return "Invalid size %s(v=0x%08X, size=%d)" % (item, self.v, self.size_words())

  def _stringify_generic(self, prefix, fields, verbosity):
    size = len(fields)
    if verbosity == 0:
      return prefix
    elif verbosity >= 2 and size <= 8:
      return "%s [%s]" % (prefix, ', '.join(["0x%08X"%f.v for f in fields]))
    else:
      return "%s (%d items)" % (prefix, size)

  def _stringify_value(self, fields, verbosity):
    return self._stringify_generic("Array/Tuple/Record/List entry", fields, verbosity)

  def _stringify_lazy_value(self, pointer, verbosity):
    if verbosity == 0:
      return "Lazy value"
    else:
      return "Lazy value (0x%08X)" % pointer

  def _stringify_lazy_result(self, fields, verbosity):
    return self._stringify_generic("Lazy result", fields, verbosity)

  def _stringify_invalid_object(self, classval, objectid, reason, verbosity):
    if verbosity == 0:
      return "Object with %s" % reason
    else:
      return "Object with %s (cls=0x%08X, oid=0x%08X)" % (reason, classval, objectid)

  def _stringify_object(self, classval, objectid, fields, verbosity):
    size = len(fields)
    if verbosity == 0:
      return "Object"
    elif verbosity >= 2 and size <= 8:
      return "Object (cls=0x%08X, oid=%d) [%s]" % (classval, objectid,
          ', '.join(["0x%08X"%f.v for f in self.fields()[2:]]))
    else:
      return "Object (cls=0x%08X, oid=%d) [%d members]" % (classval, objectid, size)

  def _stringify_empty_closure(self, fields, verbosity):
    if verbosity == 0:
      return "Empty closure"

    size = len(fields)
    if verbosity > 2 or (verbosity == 2 and size <= 8):
      return "Empty closure (%s)" % ', '.join(["0x%08X"%f.v for f in fields])
    else:
      return "Empty closure (%d items)" % size

  def _stringify_closure(self, functions, fields, verbosity):
    prefix = "Infixed closure" if len(functions) > 1 else "Closure"

    if verbosity == 0:
      return prefix

    funcnames = []
    for (function, real_function) in functions:
      if real_function != function:
        funcnames.append("%s via %s" % (real_function, function))
      else:
        funcnames.append(function)

    targets = ", ".join(funcnames)

    size = len(fields)
    if verbosity > 2 or (verbosity == 2 and size <= 8):
      return "%s to %s(%s)" % (prefix, targets,
          ', '.join(["0x%08X"%f.v for f in fields]))
    else:
      return "%s to %s(%d)" % (prefix, targets, size)

  def _stringify_closure_arity_mismatch(self, function, arity, size, reason, verbosity):
    if verbosity == 0:
      return "Closure with %s" % reason
    else:
      return "Closure to %s with %s(arity=0x%08X, size=%d)" % (function, reason, arity, size)

  def _stringify_string(self, string, verbosity):
    size = len(string)
    if verbosity == 0:
      return "String"
    elif (verbosity == 2 and size < 64) or verbosity > 2:
      return "String '%s'" % string
    else:
      return "String '%s...%d total'" % (string[:48], size)

  def _stringify_double(self, value, verbosity):
    if verbosity == 0:
      return "Double"
    else:
      return "Double: %f" % value

  def _stringify_structured_block(self, fields, verbosity):
    size = len(fields)
    if verbosity == 0:
      return "Structured block"
    elif verbosity >= 2 and size < 8:
      return "Structured block [%s]" % ', '.join(["0x%08X"%f.v for f in fields])
    else:
      return "Structured block [%d total]" % size

  @TraceMemoryError
  def try_parse(self, verbosity=0):
    #print("Trying to validate: 0x%X" % self.v)
    if self.v == 0:
      # TODO: within some sections NULL pointers are expected, e.g. global_data
      return False, "NULL pointer", []
    if self.is_int():
      return True, self._stringify_int(self.int(), verbosity), []

    # It's a block...

    if (self.v & (intnat.sizeof-1)) != 0:
      return False, self._stringify_invalid_block(int(self.v), "Unaligned pointer", verbosity), []

    ptr = self.v.cast(intnat.pointer())
    hd = self.hd()
    if hd is None:
      return False, self._stringify_invalid_block(int(self.v), "Out-of-bounds header", verbosity), []
    if try_dereference(ptr) is None:
      return False, self._stringify_invalid_block(int(self.v), "Out-of-bounds pointer", verbosity), []

    if memoryspace.have_accurate_info and not memoryspace.is_valid_data(self.v):
      memrange = memoryspace.get_range(self.v)
      return False, "Value (0x%08X) not in data memory: %s (%s)" % (self.v, str(memrange), self.resolve()), []

    word_size = self.size_words()
    if self._unsafe_field(word_size - 1) is None:
      return False, self._stringify_invalid_size(int(self.v), word_size, "of unknown type", verbosity), []

    # TODO: there's a limit to block sizes allocated on the minor heap
    if verbosity >= 2 and word_size > 1024*1024:
      print("Warning: v=0x%08X is greater than 1MiB: %d"%(self.v, word_size))

    # Pointers and size look acceptable

    tag = self.tag()
    # These if/elif conditions are ordered according to expected prevalence for performance
    # TODO: recognize and print lists properly. Now they will be printed as nested structures.
    if tag == OCamlValue.VALUE_TAG:
      fields = self.fields()
      return True, self._stringify_value(fields, verbosity), fields

    elif tag == OCamlValue.STRING_TAG:
      byte_size = self.size_bytes()
      padsize_byte = (self.v + byte_size - 1).cast(charp)
      padsize = padsize_byte.dereference()
      if padsize > intnat.sizeof:
        return False, "String with invalid padding byte: %d" % padsize, []

      real_len = byte_size - 1 - padsize
      trailing_nul = (self.v + real_len).cast(charp).dereference()
      if trailing_nul != 0:
        return False, "String without trailing NUL: %d" % trailing_nul, []

      string = self.v.cast(charp).string('latin1', 'ignore', real_len)
      return True, self._stringify_string(string, verbosity), []

    elif tag == OCamlValue.DOUBLE_TAG:
      if self.size_bytes() != doublep.target().sizeof:
        return False, self._stringify_invalid_size(int(self.v), size, "double", verbosity), []

      value = self.v.cast(doublep).dereference()
      return True, self._stringify_double(value, verbosity), []

    elif tag == OCamlValue.OBJECT_TAG:
      if word_size < 2:
        return False, self._stringify_invalid_size(int(self.v), word_size, "of object", verbosity), []

      classval = self.field(0)
      objectid = self.field(1)
      if classval.is_int():
        return False, self._stringify_invalid_object(classval.val(), objectid.val(), "invalid class id"), []

      if not objectid.is_int():
        return False, self._stringify_invalid_object(classval.val(), objectid.val(), "invalid object id"), []

      # Beware: objectid was passed raw above, but is passed as integer below
      fields = self.fields()[2:]
      return True, self._stringify_object(classval.val(), objectid.int(), fields, verbosity), fields

    elif tag == OCamlValue.CLOSURE_TAG:
      # The simplest closure contains 2 words:
      # function pointer | arity of the function
      # If data from the environment is added, it just comes after the arity.
      #
      # Some closures are special:
      # caml_curryX (partial function application) and caml_tuplifyX (let add (a,b) = ...)
      # These functions are generated by the compiler when needed and closures look like:
      # function pointer of caml_curryX | arity | function pointer of target function
      # function pointer of caml_tuplifyX | -arity | function pointer of target function
      # According to some documentation, there is also caml_apply and other forms of
      # caml_curryX_app that haven't been properly handled here yet.
      #
      # (See also documentation of the tag == OCamlValue.INFIX_TAG below)
      # When a closure contains infix tags, it's pretty hard to distinguish between that
      # and a standard closure containing an integer value that looks like an infix tag.
      # Therefore we use the simple heuristic that if we find something that looks like
      # an infix tag followed by a pointer to a code section, we treat it as an infix tag
      # and continue parsing the closure.
      if word_size < 2:
        return False, self._stringify_invalid_size(int(self.v), word_size, "closure", verbosity), []

      offset = 0
      fields = self.fields()
      functions = []
      have_more = True
      tempfunc = fields[0].val()
      while have_more:
        function = fields[0].resolve()
        arity = fields[1]
        if not arity.is_int():
          return False, self._stringify_closure_arity_mismatch(function, int(arity.v), word_size, "non-integer arity", verbosity), []
        arity = arity.int()

        if abs(arity) < 1:
          return False, self._stringify_closure_arity_mismatch(function, arity, word_size, "arity to small", verbosity), []

        if function.startswith("caml_curry"):
          skip_fields = 3
          real_function = fields[2].resolve()

        elif function.startswith("caml_tuplify"):
          arity = -arity
          real_function = fields[2].resolve()
          skip_fields = 3

        else:
          skip_fields = 2
          real_function = function

        functions.append( (function, real_function) )

        if len(fields) >= skip_fields + 2 \
          and (fields[skip_fields].val() & 0xFF) == OCamlValue.INFIX_TAG \
          and memoryspace.is_code(fields[skip_fields + 1].val()):

          infix_offset = (fields[skip_fields].val() >> 10)
          if infix_offset != offset + skip_fields + 1:
            return False, "Closure with incorrect infix size", []
          skip_fields += 1
        else:
          have_more = False

        offset += skip_fields
        fields = fields[skip_fields:]

      if len(functions) == 0:
        return False, self._stringify_empty_closure(fields, verbosity), []
      return True, self._stringify_closure(functions, fields, verbosity), fields

    elif tag == OCamlValue.LAZY_TAG:
      # This is the actual lazy value. When it is evaluated, the tag changes to either whatever
      # fit the result (probably if it fits in this OCamlValue) or into a FORWARD_TAG otherwise
      # with the field pointing to block containing the result.
      if word_size != 1:
        return False, self._stringify_invalid_size(int(self.v), word_size, "lazy value", verbosity), []

      # TODO: fields of the lazy value?
      return True, self._stringify_lazy_value(int(self.v), verbosity), self.fields()

    elif tag == OCamlValue.FORWARD_TAG:
      # This is used for forwarding to the OCamlValue containing the result of a lazy evaluation
      if word_size == 0:
        return False, self._stringify_invalid_size(int(self.v), word_size, "lazy result", verbosity), []

      fields = self.fields()
      return True, self._stringify_lazy_result(fields, verbosity), fields

    elif tag == OCamlValue.INFIX_TAG:
      # "let rec a x = ... and b y = ..." creates a closure with infixes:
      # closure header | (a) closure data (1 or more words) | infix tag | (b) closure data (1 or more words)
      # OCamlValue for a points to (a) and b points to (b)
      # The size of the infix tag is the offset in words of (b) with respect to (a)
      # For parsing, we just forward to the encapsulating closure
      closure_offset = self.size_words()
      return OCamlValue(self.v - (closure_offset*size_t.sizeof)).try_parse(verbosity)

    elif tag == OCamlValue.ABSTRACT_TAG:
      # TODO: validate more?
      return True, "Abstract %d" % word_size, []

    elif tag == OCamlValue.CUSTOM_TAG:
      # Custom values are used for things like Int64, Int32 and more. They haven't had
      # special treatment here yet. See the show() method for some more info.
      # TODO: validate more
      return True, "Custom %d" % word_size, []

    elif tag == OCamlValue.DOUBLE_ARRAY_TAG:
      if (size_bytes % (doublep.target().sizeof)) != 0:
        return False, self._stringify_invalid_size(int(self.v), size, "double array"), []
      # TODO: print actual values
      return True, "Double array", []

    else:
      fields = self.fields()
      return True, self._stringify_structured_block(fields, verbosity), fields

  @TraceMemoryError
  def show(self,recurse):
      if self.v == 0:
        print("NULL") # not a value
      elif self.is_int():
        print("%d" % self.int())
      elif self._is_list():
        print("[")
        if recurse > 0:
          self.show_seq(self.get_list(), ';', recurse-1)
        else:
          print("%d values" % self.get_list_length())
        print("]")
      else:
        t = self.tag()
        if t == 0:
          print("(")
          if recurse > 0:
            self.show_seq(self.fields(), ',', recurse-1)
          else:
            print("%d fields" % self.size_words())
          print(")")
        elif t == OCamlValue.LAZY_TAG:
          self.show_opaque("lazy")
        elif t == OCamlValue.CLOSURE_TAG:
          print("Closure(")
          if recurse > 0:
            self.show_seq(self.fields(), ',', recurse-1, raw=True)
          else:
            print("%d fields" % self.size_words())
          print(")")
        elif t == OCamlValue.OBJECT_TAG:
#	| x when x = Obj.object_tag ->
#		let fields = get_fields [] s in
#		let clasz, id, slots =
#			match fields with
#			| h::h'::t -> h, h', t 
#			| _ -> assert false
#		in
#		(* No information on decoding the class (first field).  So just print
#		* out the ID and the slots. *)
#		"Object #" ^ dump id ^ " (" ^ String.concat ", " (List.map dump slots) ^ ")"
# FIXME todo
          self.show_opaque("object")
        elif t == OCamlValue.INFIX_TAG:
          self.show_opaque("infix")
        elif t == OCamlValue.FORWARD_TAG:
          self.show_opaque("forward")
        elif t < OCamlValue.NO_SCAN_TAG:
          print("Tag%d(" % t)
          if recurse > 0:
            self.show_seq(self.fields(), ',', recurse-1)
          else:
            print("%d fields" % self.size_words())
          print(")")
        elif t == OCamlValue.STRING_TAG:
          print("%s" % self._string())
        elif t == OCamlValue.DOUBLE_TAG:
          print("%s" % self._float())
        elif t == OCamlValue.ABSTRACT_TAG:
          self.show_opaque("abstract")
        elif t == OCamlValue.CUSTOM_TAG:
          # FIXME better handle builtin caml custom values : int32, int64, etc
          try:
            sym = self.field(0).resolve()
          except:
            sym = '?'
          try:
            name = self.field(0).val().cast(charp.pointer()).dereference().string()
          except:
            name = ''
            raise
          self.show_opaque("custom " + sym + ' "' + name + '"')
        elif t == OCamlValue.FINAL_TAG:
          self.show_opaque("final")
        elif t == OCamlValue.DOUBLE_ARRAY_TAG:
          print("<float array>")
#        return "[|%s|]" % "; ".join([x.dump() for x in self.fields()])
        else:
          self.show_opaque("unknown hd=0x%X" % self.hd())

#  nil = OCamlValue.of_int(0)
#  true = OCamlValue.of_int(1)
#  false = OCamlValue.of_int(0)

class DumpOCamlValue(gdb.Command):
  """Recursively dumps runtime representation of OCaml value

                 Dump value: ml_dump [/r[N]] <value>
   Dump the array of values: ml_dump [/r[N]] <value[]> <N>
  Dump the pointer to value: ml_dump [/r[N]] <value*> 1
Dump local (stack) GC roots: ml_dump [/r[N]] local_roots

Optional /r flag controls the recursion depth limit."""

  def __init__(self):
    gdb.Command.__init__(self, "ml_dump", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL, False)

  def parse_as_addr(self,addr):
    x = gdb.parse_and_eval(addr)
    if x.address == None:
      return x.cast(size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(size_t.pointer())

  def show_ptr(self, addr, recurse):
    print("*0x%x:" % addr.cast(size_t))
    OCamlValue(addr.dereference()).show(recurse)
    print("")

  # ocaml runtime may be compiled without debug info so we have to be specific with types
  # otherwise gdb may default to 32-bit int even on 64-bit arch and inspection goes loose
  # NB values can be given by name or by address
  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)
    recurse = 1
    if len(args) > 0 and args[0].startswith("/r"):
      s = args[0][2:]
      if s == "":
        recurse = float('inf')
      else:
        recurse = int(s)
      args = args[1:]
    if len(args) < 1 or len(args) > 2:
      print("Wrong usage, see \"help ml_dump\"")
      return
    if len(args) == 2:
      addr = self.parse_as_addr(args[0])
      for i in range(int(args[1])):
        self.show_ptr(addr + i, recurse)
    else:
      if args[0] == "local_roots":
        p = gdb.parse_and_eval("*(struct caml__roots_block**)&caml_local_roots")
        while p != 0:
          print("caml_frame 0x%x" % p.cast(size_t))
          for i in range(int(p['nitems'])):
            self.show_ptr(p['tables'][i], recurse)
          p = p['next']
      else:
        addr = self.parse_as_addr(args[0])
        OCamlValue(addr).show(recurse)
        print("")

DumpOCamlValue()

class ShowOCamlHeap(gdb.Command):
  """Show some facts about OCaml heap: ml_heap [units]

Specify "w" or "words" for `units` to use OCaml words rather than bytes"""

  def __init__(self):
    gdb.Command.__init__(self, "ml_heap", gdb.COMMAND_NONE, gdb.COMPLETE_NONE, False)

  def e(self,x,t):
    return gdb.parse_and_eval("*(("+str(t)+"*)&"+x+")")

  def malloced_size(self,x):
    # see caml_aligned_malloc, FIXME Page_size = 4K assumption
    return x + 4*size_t.sizeof + 4*1024

  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)
    units = "bytes"
    unit = 1
    if len(args) > 0 and (args[0] == "words" or args[0] == "w"):
      unit = size_t.sizeof
      units = "words"

    print("     major heap size = %d %s" % (self.e("caml_stat_heap_size","intnat") / unit, units))
    print(" major heap top size = %d %s" % (self.e("caml_stat_top_heap_size","intnat") / unit, units))
    print("   total heap chunks =", self.e("caml_stat_heap_chunks","intnat"))
    print("         gray values = %d %s" % (self.e("gray_vals_size","size_t") * size_t.sizeof / unit, units))
    print("extra heap resources =", self.e("caml_extra_heap_resources","double"))
    print()
    print("minor heap :")
    minor_size = self.e("caml_minor_heap_size","size_t")
    minor_base = self.e("caml_young_base","size_t")
    y_start = self.e("caml_young_start","size_t")
    y_ptr = self.e("caml_young_ptr","size_t")
    y_end = self.e("caml_young_end","size_t")
    print("0x%x .. 0x%x - 0x%x (total %d used %d %s) malloc: 0x%x - 0x%x" % \
      (y_start, y_ptr, y_end, minor_size/unit, (y_end - y_ptr)/unit, units, minor_base, minor_base + self.malloced_size(minor_size)))
    print()
    print("major heap :")
    # the following casting is needed, otherwise gdb may sign-extend values without debug info
    v = self.e("caml_heap_start","size_t")
    i = 0
    while v != 0:
      p = gdb.Value(v - 4 * size_t.sizeof)
# typedef struct {
#   void *block;           /* address of the malloced block this chunk live in */
#   asize_t alloc;         /* in bytes, used for compaction */
#   asize_t size;          /* in bytes */
#   char *next;
# } heap_chunk_head;
      p = p.cast(size_t.pointer())
      block = p.dereference()
      size = (p + 2).dereference()
      print("%2d) chunk 0x%x - 0x%x (%d %s) malloc: 0x%x - 0x%x" % (i, v, v+size, size/unit, units, block, block+self.malloced_size(size)))
      i = i + 1
      v = (p + 3).dereference()

ShowOCamlHeap()

class ScanOCamlValue(gdb.Command):
  """Scan region of OCaml heap and show all values in it

    ml_scan [/r[N]] addr_start [bytes]

Optional /r flag controls the recursion depth limit."""

  def __init__(self):
    gdb.Command.__init__(self, "ml_scan", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL, False)

  def parse_as_addr(self,addr):
    x = gdb.parse_and_eval(addr)
    if x.address == None:
      return x.cast(size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(size_t.pointer())

  def show_val(self, addr, recurse):
    print("0x%x = " % addr.cast(size_t))
    OCamlValue(addr).show(recurse)
    print("")

  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)
    recurse = 1
    if len(args) > 0 and args[0].startswith("/r"):
      s = args[0][2:]
      if s == "":
        recurse = float('inf')
      else:
        recurse = int(s)
      args = args[1:]
    if len(args) < 1 or len(args) > 2:
      print("Wrong usage, see \"help ml_scan\"")
      return
    addr = self.parse_as_addr(args[0])
    if len(args) == 2:
        addr_end = addr + int(args[1]) / size_t.sizeof
    else:
        addr_end = addr + 64
    while addr < addr_end:
        self.show_val(addr,recurse)
        x = OCamlValue(addr)
        addr = addr + x.size_words() + 1

ScanOCamlValue()

# The functions below mimic the behavior of the OCaml run-time when performing GC.
# In C programs, memory must be handled explicitly by the developer.
# In C++ programs, tools like shared_pointer, unique_pointer, ... make memory management
# easier, yet still explicit. Memory is lost when no longer referenced.
# In languages with GC, memory management is not explicit, but handled by the run-time.
# Referenced memory is discoverable through "roots", leaving the GC with the knowledge
# that all other allocated memory is unreferenced and can be reclaimed/reused.
# In OCaml there are multiple roots, each of which is described near the function
# that discovers it below.

def get_value(name, type):
  return gdb.parse_and_eval("""*( (%s*)(&%s) )""" % (type, name))

# Global roots are global values from C-code that are registered into the GC.
def get_global_roots(roots_list_name):
  """
  Traverse the linked list of the provided global roots list and return a list of root addresses.
  """
  roots_list = gdb.parse_and_eval(roots_list_name)
  ret = []
  if roots_list == 0:
    return ret
  global_root = roots_list['forward'].dereference()
  while global_root != 0:
    root = global_root.dereference()['root'].dereference()
    ret.append((root, root+1, roots_list_name))
    global_root = global_root.dereference()['forward'].dereference()
  return ret

# Local roots are roots in the stack of C-code.
# They are automatically generated and registered from the CAMLxparam, CAMLlocal, ... macro's
# and linked together as a linked list.
def get_local_roots(roots, name):
  ret = []
  while roots != 0:
    root_struct = roots.dereference()
    for i in range(int(root_struct['ntables'])):
      for j in range(int(root_struct['nitems'])):
        value = root_struct['tables'][i][j]
        ret.append((value, value + size_t.sizeof, name))
    roots = root_struct['next']
  return ret

# See byterun/finalise.c:caml_final_do_strong_roots
# Finalisers can be registered with the GC. They are functions
# that are called when the GC determines that the value is no
# longer used and the GC is about to reclaim the memory.
# These finalisers therefore contain both a closure to a function
# and an OCamlValue to the relevant block.
def get_final_roots():
  ret = []

  try:
    young = gdb.parse_and_eval("'finalise.d.c'::young").cast(size_t) # avoid ambiguity
  except gdb.error:
    try:
      young = gdb.parse_and_eval("'finalise.c'::young").cast(size_t)
    except gdb.error:
      print("Didn't find 'finalise.c::young'. Young finaliser information is missing.")
      return ret

  for i in range(int(young)):
    final_struct = gdb.parse_and_eval("final_table[%d]" % i)
    func = final_struct['fun']
    val = final_struct['val']
    ret.append((func, func + size_t.sizeof, "final_table"))
    ret.append((val, val + size_t.sizeof, "final_table"))

  to_do_ptr = gdb.parse_and_eval("to_do_hd")
  while to_do_ptr.cast(size_t) != 0:
    to_do_struct = to_do_ptr.dereference()
    size = int(to_do_struct["size"].cast(size_t))
    items = do_to_struct["items"]
    for i in range(size):
      item_struct = (items + i).dereference()
      func = item_struct['fun']
      val = item_struct['val']
      ret.append((func, func + size_t.sizeof, "final: to_do"))
      ret.append((val, val + size_t.sizeof, "final: to_do"))

  return ret

# Dynamic global roots are global variables from dynamically linked libraries.
# They are added to a linked list of roots.
def get_dyn_globals():
  ret = []
  dyn_globals = gdb.parse_and_eval("caml_dyn_globals")
  while dyn_globals != 0:
    dyn_globals_struct = dyn_globals.dereference()
    v = dyn_globals_struct['data'].cast(size_t)
    ret.append((v, v + size_t.sizeof, "dyn_globals"))
    dyn_globals = dyn_globals_struct['next']
  return ret

# See walk_ocaml_stack() documentation.
# This function will walk the stack of the active thread first,
# followed by any other systhreads threads. All threads' information
# is kept in a linked list of thread information blocks.
# For the active thread, there are some global variables for quick
# access. Whenever acquiring or releasing the OCaml run-time lock,
# calling the GC or a C-function these global variables are updated.
# When releasing or acquiring the global run-time lock, these global
# variables are sync'd with the values from the linked list.
def walk_ocaml_stacks():
  ret = []

  # scanning for currently active thread
  sp = gdb.parse_and_eval("caml_bottom_of_stack")
  retaddr = gdb.parse_and_eval("caml_last_return_address")
  gc_regs = gdb.parse_and_eval("caml_gc_regs")
  roots = gdb.parse_and_eval("caml_local_roots")

  ret.extend(walk_ocaml_stack(sp, retaddr, gc_regs))
  ret.extend(get_local_roots(roots, "caml_local_roots"))

  # scanning for inactive threads
  # otherlibs/systhreads/st_stubs.c:caml_thread_scan_roots()
  try:
    active_thread = thread = gdb.parse_and_eval("curr_thread")
  except gdb.error:
    return ret

  while caml_thread_structp is not None:
    thread_struct = thread.dereference()

    memrange = memoryspace.get_range(thread_struct["bottom_of_stack"])
    description = "Error: unknown thread" if memrange is None else memrange.description

    descriptor = thread_struct["descr"]
    ret.append( (descriptor, descriptor + size_t.sizeof, "%s descr" % description) )
    backtrace_last_exn = thread_struct["caml_backtrace_last_exn"] # there's probably some macro at play here...
    ret.append( (backtrace_last_exn, backtrace_last_exn + size_t.sizeof, "%s backtrace_last_exn" % description) )

    if thread.cast(size_t) != active_thread.cast(size_t):
      ret.extend(walk_ocaml_stack(thread_struct["bottom_of_stack"], thread_struct["last_retaddr"], thread_struct["gc_regs"], description))
      ret.extend(get_local_roots(thread_struct["caml_local_roots"], "%s local roots" % description))

    thread = thread_struct["next"]
    if thread.cast(size_t) == active_thread.cast(size_t):
      break

  return ret

# This is a freeform translation of asmrun/roots.c:do_local_roots()
# We basically walk the stack in search of OCamlValues.
# C-code should never call the garbage collector directly. Instead
# Ocaml dynamically inserts calls to the GC wherever memory is allocated.
# The GC is then called when the minor heap runs out of space to satisfy
# the current request. Because the compiler is the only one to insert
# calls to the GC, it knows the state of the stack and CPU registers
# wrt them contains GC roots.
# It emits this information in a structure called the caml_frametable.
# This structure is walked at run-time and a hash-table is created where
# the key is the return address of the caml_call_gc() function.
# When traversing the stack, the run-time uses this information to
# locate the roots on the stack or inside registers.
def walk_ocaml_stack(sp, retaddr, gc_regs, description="stack"):
  if caml_contextp is None:
    return []
  fd_mask = gdb.parse_and_eval("caml_frame_descriptors_mask")
  def hash_retaddr(addr):
    return (addr.cast(size_t) >> 3) & fd_mask

  ret = []
  if sp == 0:
    return ret

  reg_names = {  0: "rax",  1: "rbx",  2: "rdi",  3: "rsi",  4: "rdx",  5: "rcx",  6: "r8",  7: "r9",
                 8: "r12",  9: "r13", 10: "r10", 11: "r11", 12: "rbp" }
  frame = resolve(retaddr)

  while True:
    h = hash_retaddr(retaddr)
    while True:
      d = gdb.parse_and_eval("caml_frame_descriptors[%d]"%h)
      d_struct = d.dereference()
      if d_struct["retaddr"].cast(size_t) == retaddr.cast(size_t):
        break
      h = (h+1) & fd_mask

    if d_struct["frame_size"] != 0xFFFF:
      for n in range(int(d_struct["num_live"])):
        ofs = gdb.parse_and_eval("caml_frame_descriptors[%d]->live_ofs[%d]" % (h, n)).cast(size_t)
        if ofs & 1:
          location = "[%s]" % reg_names.get(int(ofs>>1), "unknown_reg")
          root = (gc_regs.cast(size_t) + ((ofs >> 1) * size_t.sizeof)).cast(size_t.pointer()).dereference()
        else:
          location = "[sp+0x%X]" % ofs
          root = sp.cast(size_t) + ofs
        root = root.cast(size_t.pointer())
        root = root.dereference().cast(size_t)
        ret.append((root, root+size_t.sizeof, "%s(%s%s)" % (description, frame, location)))

      sp = (sp.cast(size_t) + (d_struct["frame_size"] & 0xFFFC)).cast(charp)
      retaddr = (sp.cast(size_t) - size_t.sizeof).cast(size_t.pointer()).dereference()
    else:
      next_context_p = (sp.cast(size_t) + (2 * size_t.sizeof)).cast(caml_contextp)
      next_context_struct = next_context_p.dereference()
      sp = next_context_struct["bottom_of_stack"]
      retaddr = next_context_struct["last_retaddr"]
      regs = next_context_struct["gc_regs"]
      if sp == 0:
        break
  return ret

# Compile-time global values.
# This is an array of OcamlValues to OCaml blocks. There is 1 pointer per module linked in.
# The last value is a NULL sentinel. caml_globals is part of the .data section.
def get_globals():
  ret = []
  global_data_ptr = gdb.parse_and_eval("caml_globals").cast(size_t.pointer())
  global_data = global_data_ptr.dereference()

  index = 0
  while global_data != 0:
    ret.append((global_data, global_data + size_t.sizeof, "global_data[%d]" % index))
    global_data_ptr = (global_data_ptr.cast(size_t) + size_t.sizeof).cast(size_t.pointer())
    global_data = global_data_ptr.dereference()
    index += 1

  return ret

# OCaml contains a method to dynamically add detection of more roots at run-time
# through the use of a callback function. Each user must store the previous pointer
# value, and replace the hook with its own function. Therefore, for each possible
# hook/symbol, we need to know what symbol is used to store the previous value.
# The actual discovery of the roots, however is already done in one of the above
# functions, this is merely a check that we didn't miss any roots we didn't know about.
def traverse_scan_roots_hook():
  known_hooks = {
      "caml_thread_scan_roots": "prev_scan_roots_hook", # handled in walk_ocaml_stacks()
      # more here, make sure to describe where it's handled
    }

  scan_roots_hook_ptr = gdb.parse_and_eval("caml_scan_roots_hook")
  while scan_roots_hook_ptr != 0:
    scan_roots_hook = resolve(scan_roots_hook_ptr)
    next_hook = known_hooks.get(scan_roots_hook, None)
    if next_hook is None:
      print("Unhandled root scanning function: %s" % scan_roots_hook)
      return
    scan_roots_hook_ptr = gdb.parse_and_eval(next_hook)

# See asmrun/roots.c:caml_do_roots for guidance
# This function walks over all data structures known to contain roots.
# Following this, you can walk over all OCaml values the GC knows.
# This is similar to the way the GC performs the "mark" phase.
# Another function could be written that walks over the heap in a
# similar fashion to the "sweep" phase.
# TODO: caml_globals can contain many NULL values yielding warnings/errors
def get_entry_points():
  """
  Returns a list of entry-points (aka roots) from where all live values
  can be discovered.
  The list contains tuples (start address, post-end address, source)
  with source a string identifying where the addresses were discovered.
  """
  ret = []

  # global roots
  ret.extend(get_globals())
  # dynamic global roots
  ret.extend(get_dyn_globals())
  # stacks and local roots
  ret.extend(walk_ocaml_stacks())

  # global C roots
  ret.extend(get_global_roots("caml_global_roots"))
  ret.extend(get_global_roots("caml_global_roots_young"))
  ret.extend(get_global_roots("caml_global_roots_old"))

  # finalised values
  ret.extend(get_final_roots())

  # scan_roots_hook
  traverse_scan_roots_hook()
  return ret

class ValidateHeap(gdb.Command):
  """Validates the OCaml heap
     ml_validate
  """
  def __init__(self):
    gdb.Command.__init__(self, "ml_validate", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL, False)

  def parse_as_addr(self,addr):
    x = gdb.parse_and_eval(addr)
    if x.address == None:
      return x.cast(size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(size_t.pointer())

  def _scan_range(self, todo, seen):
    values = 0
    bytes = 0
    skipped = 0

    try:
      while len(todo):
        value = todo.pop()

        if value in seen:
          skipped += 1
          continue
        seen.add(int(value.val()))


        valid, what, children = value.try_parse(3)
        if not valid:
          print("Invalid value at %s: %s" % (str(value), what))
          p = value.parent
          pindex = value.parentindex
          while p is not None:
            if isinstance(p, OCamlValue):
              _, p_what, _ = p.try_parse(3)
              print("from: 0x%08X[%d] - %s" % (p.val(), pindex, p_what))
              pindex = p.parentindex
              p = p.parent
            else:
              print("from: %s[%d]" % (str(p), pindex))
              p = None
              pindex = None
        elif len(children):
          todo.extend([child for child in children if int(child.val()) not in seen])

        if valid:
          values += 1
          bytes += 0 if value.is_int() else value.size_bytes()
    except:
      traceback.print_exc()
      raise

    return (values, skipped, bytes)

  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)

    if len(args) > 0:
      print("Wrong usage, see \"help ml_validate\"")
      return

    values = skipped = bytes = 0

    try:
      todo = collections.deque()
      seen = set()

      for (begin, end, source) in get_entry_points():
        #print("Scanning %s - %d values" % (source, (end - begin)/size_t.sizeof))

        address = begin
        while address < end:
          todo.append(OCamlValue(address, parent=source, parentindex=(address - begin)/size_t.sizeof))
          address = address + size_t.sizeof

        cur_values, cur_skipped, cur_bytes = self._scan_range(todo, seen)
        #print("Scanned %d values, skipped %d values, total of %5dB" % (cur_values, cur_skipped, cur_bytes))
        values += cur_values
        skipped += cur_skipped
        bytes += cur_bytes

    except:
      traceback.print_exc()
      raise

    print("Totals: scanned %d values, skipped %d values, total of %5dB" % (values, skipped, bytes))

ValidateHeap()

class ShowMemory(gdb.Command):
  """
  Shows memory space and its disposition
  ml_target <address|"all"> [verbosity]
  """

  def __init__(self):
    gdb.Command.__init__(self, "ml_target", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL, False)

  def parse_as_addr(self,addr):
    x = gdb.parse_and_eval(addr)
    if x.address == None:
      return x.cast(size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(size_t.pointer())

  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)

    if len(args) == 2 and args[0] == 'all':
      verbosity = int(args[1])
      address = None
    elif len(args) == 1:
      if args[0] == 'all':
        address = None
        verbosity = 0
      else:
        address = self.parse_as_addr(args[0])
    else:
      print("Wrong usage, see \"help ml_target\"")
      return

    try:
      if address is None:
        memoryspace.display(verbosity)
      else:
        memrange = memoryspace.get_range(address)
        if memrange is None:
          print("Address 0x%08X is invalid" % address)
        else:
          print("Address 0x%08X is part of: %s" % (address, str(memrange)))
    except:
        traceback.print_exc()


ShowMemory()

class FindPointersTo(gdb.Command):
  """Finds memory locations that point to a specified value:
     ml_find <value>
  """
  def __init__(self):
    gdb.Command.__init__(self, "ml_find", gdb.COMMAND_DATA, gdb.COMPLETE_SYMBOL, False)

  @TraceAll
  def invoke(self, arg, from_tty):
    init_types()
    init_memoryspace()
    args = gdb.string_to_argv(arg)

    if len(args) != 1:
      print("Wrong usage, see \"help ml_find\"")
      return

    value = int(args[0])
    pattern = struct.pack("L", value)
    locations = memoryspace.search_memory_of_types(pattern, *MemoryType.all())
    for location in locations:
      memrange = memoryspace.get_range(location)
      print("Found at 0x%08X in %s" % (location, memrange.description))

FindPointersTo()
