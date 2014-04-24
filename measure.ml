(**
  Simple module to measure code speed and allocation rate
 
  http://ygrek.org.ua/p/code/measure.ml
  2011-08-08
*)

open Printf
open Gc

let bytes_f f = (* oh ugly *)
  let a = abs_float f in
  if a < 1024. then sprintf "%dB" (int_of_float f) else
  if a < 1024. *. 1024. then sprintf "%dKB" (int_of_float (f /. 1024.)) else
  if a < 1024. *. 1024. *. 1024. then sprintf "%.1fMB" (f /. 1024. /. 1024.) else
  sprintf "%.1fGB" (f /. 1024. /. 1024. /. 1024.)

let bytes x = bytes_f (float_of_int x)
let bytes_64 x = bytes_f (Int64.to_float x)

let words_f f =
  bytes_f (f *. (float_of_int (Sys.word_size / 8)))

let words x = words_f (float_of_int x)

let gc_diff st1 st2 =
  let allocated st = st.minor_words +. st.major_words -. st.promoted_words in
  let a = allocated st2 -. allocated st1 in
  let minor = st2.minor_collections - st1.minor_collections in
  let major = st2.major_collections - st1.major_collections in
  let compact = st2.compactions - st1. compactions in
  let heap = st2.heap_words - st1.heap_words in
  Printf.sprintf "allocated %7s, heap %7s, collect %2d %4d %5d" (words_f a) (words heap) compact major minor

let measure f x =
  Gc.compact ();
  let st = Gc.quick_stat () in
  let t1 = Unix.gettimeofday () in
  let () = f x in
  let t2 = Unix.gettimeofday () in
  let st2 = Gc.quick_stat () in
  sprintf "%s, elapsed %.3f sec" (gc_diff st st2) (t2 -. t1)

let show name f x =
  printf "%12s : %s\n%!" name (measure f x)

(**
  Example usage:
 
let src = "We should forget about small efficiencies, say about 97% of the time: premature optimization is the root of all evil"
 
let run f = for i = 1 to 1_000_000 do ignore (f () : string) done
let scanf () = Scanf.sscanf src "%s@:" (fun s -> s)
let sub () = String.sub src 0 (String.index src ':')
 
let () =
  Measure.show "scanf" run scanf;
  Measure.show "sub" run sub;
  ()
 
  Compile:
 
ocamlopt unix.cmxa measure.ml bench.ml -o bench
 
  Result:
 
       scanf : allocated   2.2GB, heap      0B, collect  0 1419  8888, elapsed 2.072 sec
         sub : allocated  76.3MB, heap      0B, collect  0    0   305, elapsed 0.162 sec
 
*)
