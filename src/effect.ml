
module Map = Map.Make(String)
module T = Uterm
module H = Helper
open Why3
open Ptree
let exn_name = "exn"

let n_vcs = ref 0

let vc () = n_vcs := !n_vcs + 1; "vc" ^ (string_of_int (!n_vcs))

(**auxiliary variables and functions to map effect names to the types they return*)
let effect_types : (pty Map.t) ref = ref Map.empty

let tl_ref_types : (pty Map.t) ref = ref Map.empty

let arg_fun_types : (pty Map.t) ref = ref Map.empty

let map_effect e t =
  effect_types := Map.add e t (!effect_types)

let map_ref_type r t =
  print_endline r;
  let t = 
    match t with 
    |PTtyapp(Qident id, l) -> PTtyapp(Qident({id with id_loc = Why3.Loc.dummy_position}), l)
    | _ -> t in 
  tl_ref_types := Map.add r t (!tl_ref_types)

let map_fun_type f t =
  let t = T.defun_type t in 
  arg_fun_types := Map.add f t (!arg_fun_types)

let get_ref_type r = 
  Map.find r (!tl_ref_types)

let get_effect_type e = 
  Map.find e (!effect_types)

let get_state_type () =
  let seq = Map.to_seq !tl_ref_types in
  let ptyl = List.of_seq (Seq.map (fun (_, pty) -> pty) seq) in 
  PTtuple ptyl 

let writes_clause () = 
  let seq = Map.to_seq !tl_ref_types in 
  List.of_seq (
    Seq.map (fun (s, _) -> H.mk_tid s) seq
  )

let pattern_of_string s =
  T.mk_pattern (Pvar s)

(** Creates a term that is a tuple consisting of the values of all mutable references
    @param is_old true if we want the old values *)
let mk_state_term is_old =
  let seq = Map.to_seq !tl_ref_types in
  let tl = List.of_seq (Seq.map (fun (s, _) -> 
    let id = H.mk_tid s in 
    let bang = H.mk_tid (Why3.Ident.op_prefix "!") in 
    let t = T.mk_term (Tapply (bang, id)) in 
    if is_old then T.mk_term (Tat(t, T.mk_id "'Old")) else t) seq) in 
  T.mk_term (Ttuple tl)

(** Given a term {!t} creates a new term term
    {!match state with |(v1, v2, ...) -> t}
    
    @param is_old if we are going to pattern match over the old state or the new state 
    @param t the term we want to wrap the pattern match around 
    *)
let wrap ?(s_name = None) is_old t =
  let s = 
    match s_name with 
    |Some s -> s
    |None -> if is_old then "old_state" else "state" in 
  let prefix = if is_old then "old_" else "" in 
  let seq = Map.to_seq !tl_ref_types in
  let vl = List.of_seq (Seq.map (fun (s, _) -> T.mk_pattern (Pvar (T.mk_id (prefix ^ s)))) seq) in 
  let pat = T.mk_pattern (Ptuple vl) in 
  T.mk_term (Tcase (H.mk_tid s, [pat, t]))

let state_exp n e = 
  let seq = Map.to_seq !tl_ref_types in
  let tl = List.of_seq (Seq.map (fun (s, _) -> 
    let id = H.mk_eid s in 
    let bang = H.mk_eid (Why3.Ident.op_prefix "!") in 
    H.mk_expr (Eapply(bang, id)) 
    ) seq) in 
  let s = H.mk_expr (Etuple tl) in 
  H.mk_expr (
    Elet(H.mk_id n, true, Expr.RKnone, s, e)
  )