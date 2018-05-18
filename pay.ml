(* Track group expenses

Consider example.ml :

```
#!/usr/bin/env ocaml
#use "pay.ml"

let a = "Alice"
let b = "Bob"
let m = "Mallory"

let () = [
  on "New Year", "cake", share 58_00 [a;b;m], [a, 66_00];
  on "Jan 2", "cinema", share' [a;b], [b, 40_00];
  on "Jan 10", "pizza", bill 50_00 [a, 25_00; b, 25_00 / 2; m, 25_00/2], [m, 55_00];
]
|> report_argv
```

Get the global view and final balance:

```
$ ./example.ml
[New Year]  cake                 : 58.00 (3 pax), Alice paid 66.00 tipping 13%
[   Jan 2]  cinema               : 40.00 (2 pax), Bob paid 40.00
[  Jan 10]  pizza                : 50.00 (3 pax), Mallory paid 55.00 tipping 10%

Bob -15.75
Alice -3.50
Mallory 19.25
```

Report for one participant:

```
$ ./example.ml report Bob
[New Year]  -22.00 =  -22.00  : cake                 : 58.00 (3 pax), Alice paid 66.00 tipping 13%
[   Jan 2]  +20.00 =   -2.00  : cinema               : 40.00 (2 pax), Bob paid 40.00
[  Jan 10]  -13.75 =  -15.75  : pizza                : 50.00 (3 pax), Mallory paid 55.00 tipping 10%
```
*)

open Printf

let fail fmt = ksprintf failwith fmt

let money x = (if x < 0 then "-" else "") ^ sprintf "%d.%02d" (abs x / 100) (abs x mod 100)
let delta x = (if x > 0 then "+" else "") ^ money x
let pr fmt = ksprintf print_endline fmt

let sum = List.fold_left (fun acc (_,x) -> acc + x) 0

let compute ?track l =
  let h = Hashtbl.create 10 in
  let bal who = try Hashtbl.find h who with Not_found -> 0 in
  let tracked = ref 0 in
  l |> List.iter begin fun (`Date date,where,party,payer) ->
    assert (payer <> []);
    let paid = sum payer in
    let (bill,party) =
      match party with
      | `Items (bill,l) -> assert (l<>[]); bill, l
      | `Share' l -> assert (l<>[]); paid, l |> List.map (fun who -> who, paid / List.length l)
      | `Share (bill, l) -> assert (l<>[]); bill, l |> List.map (fun who -> who, bill / List.length l)
    in
    let total = sum party in
    let extra = bill - total in
    let taxes =
      if extra = 0 then
        ""
      else if extra < List.length party then (* due to integer division, passed onto payer *)
(*         sprintf " incl. extra %s" (money extra) *)
        ""
      else
        sprintf " incl. extra %s (%.2f%%)" (money extra) (100. *. float extra /. float total)
    in
    let tips = if paid - bill <> 0 then sprintf " tipping %d%%" (100 * (paid - bill) / bill) else "" in
    if paid < bill then fail "bill %s < paid %s" (money bill) (money paid);
    if bill < total then fail "bill %s < total %s" (money bill) (money total);
    party |> List.iter (fun (who,x) -> Hashtbl.replace h who (bal who - x - x * (paid - total) / total));
    payer |> List.iter (fun (who,x) -> Hashtbl.replace h who (bal who + x));
    let track =
      match track with
      | None -> Some ""
      | Some name when bal name = 0 && !tracked = 0 -> None
      | Some name ->
        let diff = bal name - !tracked in
        tracked := bal name;
        Some (sprintf "%7s = %7s  :" (if diff = 0 then "" else delta diff) (money @@ bal name))
    in
    begin match track with
    | None -> ()
    | Some track ->
      pr "[%8s] %s %-20s : %s (%d pax)%s, %s paid %s%s"
        date track where (money bill) (List.length party) taxes (String.concat " " @@ List.map fst payer) (money paid) tips;
    end
  end;
  pr "";
  h

let show_standings h =
  Hashtbl.fold (fun k v acc -> (k,v)::acc) h []
  |> List.sort (fun (_,a) (_,b) -> compare a b)
  |> List.iter (fun (who,x) -> pr "%s %s" who (money x))

let report_paid name ledger =
  let x = List.fold_left begin fun acc (_,_,_,payer) ->
    List.fold_left (fun acc (who,x) -> acc + if who = name then x else 0) acc payer
  end 0 ledger
  in
  pr "%s %s" name (money x)

let on x = `Date x
let items l = `Items (sum l, l)
let bill d l = `Items (d,l)
let share' l = `Share' l
let share bill l = `Share (bill, l)

let report_argv ledger =
  match List.tl @@ Array.to_list Sys.argv with
  | "report"::name::[]
  | name::[] -> show_standings @@ compute ~track:name ledger
  | [] -> show_standings @@ compute ledger
  | "paid"::name::[] -> report_paid name ledger
  | _ -> prerr_endline "wat?"; exit 2
