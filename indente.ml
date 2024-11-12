#! /usr/bin/env b0caml
#directory "+ocaml/compiler-libs"

open Printf

let loc { Parsetree.pexp_loc = loc; _ } = Location.get_pos_info loc.loc_start
let col expr = let (_,_,c) = loc expr in c

let iter = { Ast_iterator.default_iterator with
  expr = fun iter expr ->
    begin match expr with
    | { pexp_desc = Pexp_sequence ({ pexp_desc = Pexp_ifthenelse (_cond,e_then,e_else); _ } as e_if, next); _ } ->
      let last = Option.value ~default:e_then e_else in
      if col last = col next && col next <> col e_if then
        let (file,line,_) = loc next in
        printf "Suspicious indentation of next expression after if at %s %d\n%!" file line
    | _ -> ()
    end;
    Ast_iterator.default_iterator.expr iter expr
  }

let parse file =
  iter.structure iter @@ Pparse.parse_implementation ~tool_name:"indetect" file

let () =
   Sys.argv |> Array.iteri begin fun i file ->
     if i <> 0 then try parse file with exn -> fprintf stderr "Failed to parse %s : %s\n%!" file (Printexc.to_string exn)
   end
