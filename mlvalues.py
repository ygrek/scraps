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
#    python x = OCamlValue(gdb.parse_and_eval("caml_globals")); print x.size()
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

# gdb.Type's used often throughout the script
intnat = size_t = charp = doublep = heap_chunk_head_p = None

# do not lookup types at class level cause this script may be run before
# the inferior image is loaded and gdb can't know sizeof(long) in advance
def init_types():
  global intnat, size_t, charp, doublep, heap_chunk_head_p

  if doublep is not None:
    return

  try:
    heap_chunk_head_p = gdb.lookup_type("heap_chunk_head").pointer()
  except:
    print("Didn't find 'heap_chunk_head'. Major heap walking is unavailable")
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

# This class represents gdb.Value as OCaml value.
# Analogue to stdlib Obj module.
#
# It probably contains more casts than strictly necessary,
# but after all who am I to understand python type system?
# Just a mere OCaml coder. And this is my first python program.
class OCamlValue:

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

  def __init__(self,v):
    # do not lookup types at class level cause this script may be run before
    # the inferior image is loaded and gdb can't know sizeof(long) in advance
    self.intnat = gdb.lookup_type("intnat")
    self.t_charp = gdb.lookup_type("char").pointer()
    self.t_doublep = gdb.lookup_type("double").pointer()
    if type(v) == type(0):
      self.v = gdb.Value(v)
    else:
      self.v = v.cast(self.intnat)

  def is_int(self):
    return self.v & 1 != 0

  def is_block(self):
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
    return OCamlValue.of_int(x != 0)

  def int(self):
    assert self.is_int()
    return self.v >> 1

  def val(self):
    return self.v

  def show_string(self,enc='latin1'):
    assert self.tag() == OCamlValue.STRING_TAG
    temp = self.bsize() - 1
    slen = temp - (self.v + temp).cast(self.t_charp).dereference()
    assert 0 == (self.v + slen).cast(self.t_charp).dereference()
    if slen <= 1024:
        s = self.v.cast(self.t_charp).string(enc, 'ignore', slen)
        print s.__repr__(),
    else:
        s = self.v.cast(self.t_charp).string(enc, 'ignore', 256)
        print "%s..<%d bytes total>" % (s.__repr__(), slen),

  def float(self):
    assert self.tag() == OCamlValue.DOUBLE_TAG
    # FIXME test
    return self.v.cast(self.t_doublep).dereference()

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
    return (self.v - self.intnat.sizeof).cast(self.intnat.pointer()).dereference()

  def tag(self):
    if self.is_int():
      return OCamlValue.INT_TAG
    else:
      return self.hd() & 0xFF

  def unsafe_field(self,i):
    x = (self.v + i * self.intnat.sizeof).cast(self.intnat.pointer()).dereference()
    return OCamlValue(x)

  def field(self,i):
    assert self.is_block()
    assert self.tag () != OCamlValue.DOUBLE_ARRAY_TAG # FIXME not implemented
    n = self.size()
    if i < 0 or i >= n:
      raise IndexError("field %d size %d" % (i,n))
    return self.unsafe_field(i)
    #t = self.intnat.array(n).pointer()
    #return OCamlValue(self.v.cast(t).dereference()[i])

  def fields(self):
    assert self.is_block()
    assert self.tag () != OCamlValue.DOUBLE_ARRAY_TAG # FIXME not implemented
    a = []
    for i in range(self.size()):
      a.append(self.unsafe_field(i))
    return a

  def size(self):
    assert self.is_block()
    return self.hd() >> 10

  def bsize(self):
    return self.size() * self.intnat.sizeof

  def is_list(self):
    if self.is_int():
      return self.int() == 0
    else:
      return self.size() == 2 and self.tag() == 0 and self.field(1).is_list()

  def get_list(self):
    a = []
    l = self
    while l.is_block():
      a.append(l.field(0))
      l = l.field(1)
    return a

  def get_list_length(self):
    n = 0
    l = self
    while l.is_block():
      n+=1
      l = l.field(1)
    return n

  def resolve(self):
    symbol = gdb.execute('info symbol ' + str(self.val()),False,True).split(' ',1)[0]
    if symbol == "No": # FIXME "No symbol matches"
      return "0x%x" % self.val()
    else:
      return "%s" % symbol

  def show_opaque(self,s):
    print "<%s at 0x%x>" % (s,self.val()),

  def show_all(self,seq,delim,recurse,raw=False):
    for i, x in enumerate(seq):
      if i:
        print delim,
      if raw:
        print x.resolve(),
      else:
        x.show(recurse)

  @TraceMemoryError
  def show(self,recurse):
    try:
      if self.v == 0:
        print "NULL" # not a value
      elif self.is_int():
        print "%d" % self.int(),
      elif self.is_list():
        print "[",
        if recurse > 0:
          self.show_all(self.get_list(), ';', recurse-1)
        else:
          print "%d values" % self.get_list_length(),
        print "]",
      else:
        t = self.tag()
        if t == 0:
          print "(",
          if recurse > 0:
            self.show_all(self.fields(), ',', recurse-1)
          else:
            print "%d fields" % self.size(),
          print ")",
        elif t == OCamlValue.LAZY_TAG:
          self.show_opaque("lazy")
        elif t == OCamlValue.CLOSURE_TAG:
          print "Closure(",
          if recurse > 0:
            self.show_all(self.fields(), ',', recurse-1, raw=True)
          else:
            print "%d fields" % self.size(),
          print ")",
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
          print "Tag%d(" % t,
          if recurse > 0:
            self.show_all(self.fields(), ',', recurse-1)
          else:
            print "%d fields" % self.size(),
          print ")",
        elif t == OCamlValue.STRING_TAG:
          self.show_string()
        elif t == OCamlValue.DOUBLE_TAG:
          print "%f" % self.float(),
        elif t == OCamlValue.ABSTRACT_TAG:
          self.show_opaque("abstract")
        elif t == OCamlValue.CUSTOM_TAG:
          # FIXME better handle builtin caml custom values : int32, int64, etc
          try:
            sym = self.field(0).resolve()
          except:
            sym = '?'
          try:
            name = self.field(0).val().cast(self.t_charp.pointer()).dereference().string()
          except:
            name = ''
            raise
          self.show_opaque("custom " + sym + ' "' + name + '"')
        elif t == OCamlValue.FINAL_TAG:
          self.show_opaque("final")
        elif t == OCamlValue.DOUBLE_ARRAY_TAG:
          print "<float array>",
#        return "[|%s|]" % "; ".join([x.dump() for x in self.fields()])
        else:
          self.show_opaque("unknown tag %d size %d" % (t,self.size()))
    except gdb.MemoryError as exn:
      print '<<gdb.MemoryError : %s>>' % exn,

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
    print ""

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
      print "Wrong usage, see \"help ml_dump\""
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
        print ""

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

    print "     major heap size = %d %s" % (self.e("caml_stat_heap_size","intnat") / unit, units)
    print " major heap top size = %d %s" % (self.e("caml_stat_top_heap_size","intnat") / unit, units)
    print "   total heap chunks =", self.e("caml_stat_heap_chunks","intnat")
    print "         gray values = %d %s" % (self.e("gray_vals_size","size_t") * self.size_t.sizeof / unit, units)
    print "extra heap resources =", self.e("caml_extra_heap_resources","double")
    print
    print "minor heap :"
    minor_size = self.e("caml_minor_heap_size","size_t")
    minor_base = self.e("caml_young_base","size_t")
    y_start = self.e("caml_young_start","size_t")
    y_ptr = self.e("caml_young_ptr","size_t")
    y_end = self.e("caml_young_end","size_t")
    print "0x%x .. 0x%x - 0x%x (total %d used %d %s) malloc: 0x%x - 0x%x" % \
      (y_start, y_ptr, y_end, minor_size/unit, (y_end - y_ptr)/unit, units, minor_base, minor_base + self.malloced_size(minor_size))
    print
    print "major heap :"
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
      print "%2d) chunk 0x%x - 0x%x (%d %s) malloc: 0x%x - 0x%x" % (i, v, v+size, size/unit, units, block, block+self.malloced_size(size))
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
    print ""

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
      print "Wrong usage, see \"help ml_scan\""
      return
    addr = self.parse_as_addr(args[0])
    if len(args) == 2:
        addr_end = addr + int(args[1]) / size_t.sizeof
    else:
        addr_end = addr + 64
    while addr < addr_end:
        self.show_val(addr,recurse)
        x = OCamlValue(addr)
        addr = addr + x.size() + 1

ScanOCamlValue()
