(**
http://www.bittorrent.org/beps/bep_0003.html
*)

(* open Prelude *)

let (>>) x f = f x
let fail fmt = Printf.ksprintf failwith fmt

open Printf
open ExtLib

module type Number = sig 
  type t 
  val neg : t -> t
  val of_int : int -> t
  val to_int : t -> int
  val of_string : string -> t 
  val to_string : t -> string 
  val zero : t
  val add : t -> t -> t
  val mul : t -> t -> t
end

module Make(N : Number) = struct

type t =
  | S of string
  | I of N.t
  | L of t list
  | D of (string * t) list

let decode_stream ?(hints=[]) chars =
  let ten = N.of_int 10 in
  let digit c = N.of_int (Char.code c - Char.code '0') in
  let rec loop acc = parser
    | [< x=parse_one; t; >] -> loop (x::acc) t
    | [< >] -> List.rev acc
  and parse_one = parser
    | [< s=parse_string >] -> S s
    | [< ''i'; n=parse_int_num; ''e' >] -> I n
    | [< ''l'; l=loop []; ''e' >] -> L l
    | [< ''d'; d=loop_d []; ''e' >] -> D d
  and loop_d acc = parser
    | [< k=parse_string; v=parse_one; t >] -> loop_d ((k,v) :: acc) t
    | [< >] -> List.rev acc
  and parse_string = parser 
    | [< n = parse_pos_num; '':'; s = take (N.to_int n) >] -> s
  and parse_int_num = parser
    | [< ''-'; x = parse_pos_num >] -> N.neg x
    | [< x = parse_pos_num >] -> x
  and parse_pos_num = parser
    | [< ''0' >] -> N.zero
    | [< ''1'..'9' as c; n = parse_digits (digit c) >] -> n
  and parse_digits n = parser
    | [< ''0'..'9' as c; t >] -> parse_digits (N.add (N.mul n ten) (digit c)) t
    | [< >] -> n
  and take n chars =
    let s = String.make n '\000' in
    for i = 0 to n-1 do s.[i] <- Stream.next chars done; s
  in
  let main () = 
    let r = parse_one chars in 
    if not (List.mem `IgnoreTail hints) then Stream.empty chars;
    r
  in
  let show () =
    let tail = Stream.npeek 10 chars >> List.map (String.make 1) >> String.concat "" in
    sprintf "Position %u : %s" (Stream.count chars) tail
  in
  try 
    main ()
  with 
  | Stream.Error _ | Stream.Failure -> failwith (show ())

let rec print out = 
  let pr fmt = IO.printf out fmt in
  function
  | I n -> pr "%s " (N.to_string n)
  | S s -> pr "\"%s\" " (String.slice ~last:10 s)
  | L l -> pr "( "; List.iter (print out) l; pr ") "
  | D d -> pr "{ "; List.iter (fun (k,v) -> pr "%s: " k; print out v) d; pr "} "

let to_string t =
  let module B = Buffer in
  let b = B.create 100 in
  let puts s = bprintf b "%u:%s" (String.length s) s in
  let rec put = function
    | I n -> bprintf b "i%se" (N.to_string n)
    | S s -> puts s
    | L l -> B.add_char b 'l'; List.iter put l; B.add_char b 'e'
    | D d ->
      B.add_char b 'd';
      List.iter (fun (s,x) -> puts s; put x) (List.sort ~cmp:(fun (s1,_) (s2,_) -> compare s1 s2) d); 
      B.add_char b 'e'
  in
  put t; B.contents b

(** @raise exn on error *)
let decode s =
  Stream.of_string s >> decode_stream

let key s k v =
  match v with
  | D l -> k (try List.assoc s l with Not_found -> fail "no key '%s'" s)
  | _ -> fail "not a dictionary"

let int = function I n -> n | _ -> fail "int"
let str = function S s -> s | _ -> fail "str"
let list k v = match v with L l -> k l | _ -> fail "list"
let listof k v = match v with L l -> List.map k l | _ -> fail "listof"
let dict k v = match v with D l -> k l | _ -> fail "dict"

end

include Make(Int64)

