# Inspect OCaml heap and values in GDB
# 2016/01/17
#
# https://github.com/ygrek/scraps/blob/master/mlvalues.py
# (c) 2011 ygrek
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
      return x.cast(self.size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(self.size_t.pointer())

  def show_ptr(self, addr, recurse):
    print "*0x%x:" % addr.cast(self.size_t),
    OCamlValue(addr.dereference()).show(recurse)
    print ""

  # ocaml runtime may be compiled without debug info so we have to be specific with types
  # otherwise gdb may default to 32-bit int even on 64-bit arch and inspection goes loose
  # NB values can be given by name or by address
  def invoke(self, arg, from_tty):
    self.size_t = gdb.lookup_type("size_t")
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
          print "caml_frame 0x%x" % p.cast(self.size_t)
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
    return x + 4*self.size_t.sizeof + 4*1024

  def invoke(self, arg, from_tty):
    self.size_t = gdb.lookup_type("size_t")
    args = gdb.string_to_argv(arg)
    units = "bytes"
    unit = 1
    if len(args) > 0 and (args[0] == "words" or args[0] == "w"):
      unit = self.size_t.sizeof
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
      p = gdb.Value(v - 4 * self.size_t.sizeof)
# typedef struct {
#   void *block;           /* address of the malloced block this chunk live in */
#   asize_t alloc;         /* in bytes, used for compaction */
#   asize_t size;          /* in bytes */
#   char *next;
# } heap_chunk_head;
      p = p.cast(self.size_t.pointer())
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
      return x.cast(self.size_t.pointer())
    else: # l-value, prevent short read when no debugging info
      return gdb.parse_and_eval("*((size_t*)&"+addr+")").cast(self.size_t.pointer())

  def show_val(self, addr, recurse):
    print "0x%x = " % addr.cast(self.size_t),
    OCamlValue(addr).show(recurse)
    print ""

  def invoke(self, arg, from_tty):
    self.size_t = gdb.lookup_type("size_t")
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
        addr_end = addr + int(args[1]) / self.size_t.sizeof
    else:
        addr_end = addr + 64
    while addr < addr_end:
        self.show_val(addr,recurse)
        x = OCamlValue(addr)
        addr = addr + x.size() + 1

ScanOCamlValue()
