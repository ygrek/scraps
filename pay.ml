open Printf

let money x = sprintf "%d.%02d" (x/100) (abs x mod 100)
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
    assert (paid >= bill);
    assert (bill >= total);
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

let on x = `Date x
let items l = `Items (sum l, l)
let bill d l = `Items (d,l)
let share' l = `Share' l
let share bill l = `Share (bill, l)

let report_argv ledger =
  let r =
    match List.tl @@ Array.to_list Sys.argv with
    | "report"::name::[]
    | name::[] -> compute ~track:name ledger
    | [] -> compute ledger
    | _ -> prerr_endline "wat?"; exit 2
  in
  show_standings r
