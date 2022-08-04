
module Map = Map.Make(String)
module T = Uterm
module H = Helper
open Why3
open Ptree
let exn_name = "exn"

let vc = 
  let n_vcs = ref 0 in 
  fun () -> n_vcs := !n_vcs + 1; "vc" ^ (string_of_int (!n_vcs))

(**auxiliary variables and functions to map effect names to the types they return*)
let effect_types : (pty Map.t) ref = ref Map.empty

let tl_ref_types : (pty Map.t) ref = ref Map.empty

let arg_fun_types : (pty Map.t) ref = ref Map.empty

let effect_terms : ((term list * term list) Map.t) ref = ref Map.empty

let map_terms e pre post =
  effect_terms := Map.add e (pre, post) !effect_terms  

let map_effect e t =
  effect_types := Map.add e t (!effect_types)


let map_ref_type r t =
  print_endline r;
  let t = 
    match t with 
    |PTtyapp(Qident id, l) -> PTtyapp(Qident({id with id_loc = Why3.Loc.dummy_position}), l)
    | _ -> t in 
  tl_ref_types := Map.add r t (!tl_ref_types)

let map_arg_type f t =
  let t = T.defun_type t in 
  arg_fun_types := Map.add f t (!arg_fun_types)

let flush_fun_types () =
  arg_fun_types := Map.empty

let is_defun v =
  match Map.find_opt v !arg_fun_types with 
  |Some (PTtyapp (Qident ({id_str="lambda";_}), _)) -> true 
  |_ -> false 

let get_ref_type r = 
  Map.find r (!tl_ref_types)

let get_effect_type e = 
  Map.find e (!effect_types)

let get_state_type () =
  let seq = Map.to_seq !tl_ref_types in
  let _ptyl = List.of_seq (Seq.map (fun (_, pty) -> pty) seq) in
  PTtyapp(Qident (H.mk_id "_state"), [])

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
    let t = if is_old then T.mk_term (Tat(t, T.mk_id "'Old")) else t in 
    Qident (H.mk_id ("_" ^ s)), t) seq) in 
  T.mk_term (Trecord tl)

(* Given a term {!t} creates a new term term
    {!match state with |(v1, v2, ...) -> t}
    
    @param is_old if we are going to pattern match over the old state or the new state 
    @param t the term we want to wrap the pattern match around 
    
let wrap ?(s_name = None) is_old t =
  if t.term_desc = Ttrue then t else 
  let s = 
    match s_name with 
    |Some s -> s
    |None -> if is_old then "old_state" else "state" in 
  let prefix = if is_old then "old_" else "" in 
  let seq = Map.to_seq !tl_ref_types in
  let vl = List.of_seq (Seq.map (fun (s, _) -> T.mk_pattern (Pvar (T.mk_id (prefix ^ s)))) seq) in 
  (*if vl = [] then t else*) 
  let pat = T.mk_pattern (Ptuple vl) in 
  T.mk_term (Tcase (H.mk_tid s, [pat, t]))*)

let state_exp n e = 
  let seq = Map.to_seq !tl_ref_types in
  let tl = List.of_seq (Seq.map (fun (s, _) -> 
    let id = H.mk_eid s in 
    let bang = H.mk_eid (Why3.Ident.op_prefix "!") in 
    Qident (H.mk_id ("_" ^ s)), H.mk_expr (Eapply(bang, id)) 
    ) seq) in 
  let s = H.mk_expr (Erecord tl) in 
  H.mk_expr (
    Elet(H.mk_id n, true, Expr.RKnone, s, e)
  )

  let mk_post_term arg_name =
    T.mk_term 
      (Tidapp (Qident (T.mk_id "post"), 
      [H.mk_tid "f"; 
      H.mk_tid arg_name; 
      H.mk_tid "old_state"; 
      H.mk_tid "state"; 
      H.mk_tid "result"])) 

let mk_pre_term arg_name =
  T.mk_term (
    (Tidapp (Qident (T.mk_id "pre"), 
      [H.mk_tid "f"; 
      H.mk_tid arg_name; 
      H.mk_tid "state"])
  ))