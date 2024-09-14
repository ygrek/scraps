#! /usr/bin/env ocamlscript

let () =
  match Sys.argv with
  | [|_;k|] ->
    let rec loop acc =
      match input_line stdin with
      | exception End_of_file -> List.rev acc
      | s -> loop (s::acc)
    in
    begin match loop [] with
    | [] -> exit 1
    | first::_ as l ->
      let rec next = function
      | x::xs when x = k -> (match xs with [] -> first | y::_ -> y)
      | _::xs -> (* Printf.eprintf "skipping %S <> %S" y k; *) next xs
      | [] -> first
      in
      print_endline @@ next l
    end
  | _ ->
    prerr_endline "next.ml.exe <key>";
    prerr_endline "Outputs the next line from stdin after the <key>, first one if <key> is the last."
