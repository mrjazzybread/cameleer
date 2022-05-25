
module Map = Map.Make(String)
module T = Uterm
open Why3.Ptree
let eff_name = "eff"

let n_vcs = ref 0

let vc () = n_vcs := !n_vcs + 1; "vc" ^ (string_of_int (!n_vcs))

(**auxiliary variables and functions to map effect names to the types they return*)
let effect_types : (pty Map.t) ref = ref Map.empty

let tl_ref_types : (pty Map.t) ref = ref Map.empty

let map_effect e t =
  effect_types := Map.add e t (!effect_types)

let map_ref_type r t =
  let t = 
    match t with 
    |PTtyapp(Qident id, l) -> PTtyapp(Qident({id with id_loc = Why3.Loc.dummy_position}), l)
    | _ -> t in 
  tl_ref_types := Map.add r t (!tl_ref_types)


let get_ref_type r = 
  Map.find r (!tl_ref_types)

let get_effect_type e = 
  Map.find e (!effect_types)

let get_state_type () =
  let seq = Map.to_seq !tl_ref_types in
  let ptyl = List.of_seq (Seq.map (fun (_, pty) -> pty) seq) in 
  PTtuple ptyl 

let term_of_string s =
  T.mk_term (Tident (Qident (T.mk_id s)))

let pattern_of_string s =
  T.mk_pattern (Pvar s)

let mk_state_term is_old =
  let seq = Map.to_seq !tl_ref_types in
  let tl = List.of_seq (Seq.map (fun (s, _) -> 
    let id = term_of_string s in 
    let bang = term_of_string (Why3.Ident.op_prefix "!") in 
    let t = T.mk_term (Tapply (bang, id)) in 
    if is_old then T.mk_term (Tat(t, T.mk_id "'Old")) else t) seq) in 
  T.mk_term (Ttuple tl)

let wrap is_old t =
  let s = if is_old then "old_state" else "state" in 
  let prefix = if is_old then "old_" else "" in 
  let seq = Map.to_seq !tl_ref_types in
  let vl = List.of_seq (Seq.map (fun (s, _) -> T.mk_pattern (Pvar (T.mk_id (prefix ^ s)))) seq) in 
  let pat = T.mk_pattern (Ptuple vl) in 
  T.mk_term (Tcase (term_of_string s, [pat, t]))