open Why3
open Ptree

let dummy_loc = Loc.dummy_position
let mk_term ?(term_loc = dummy_loc) term_desc = { term_desc; term_loc }

let mk_id ?(id_ats = []) ?(id_loc = dummy_loc) id_str =
  { id_str; id_ats; id_loc }

let mk_expr ?(expr_loc = dummy_loc) expr_desc = { expr_desc; expr_loc }

let mk_pattern ?(pat_loc = dummy_loc) pat_desc = { pat_desc; pat_loc }
let mk_why_post t = 
  dummy_loc, [mk_pattern (Pvar (mk_id "result")), t]

let mk_tid s = 
  mk_term (Tident (Qident (mk_id s)))

let mk_eid s =
  mk_expr (Eident (Qident (mk_id s)))
let pre = mk_tid "pre"
let post = mk_tid "post"
 

let fold_terms terms = 
  let dtand = Why3.Dterm.DTand in 
  if terms = [] then mk_term Ttrue else
    List.fold_left 
      (fun acc t -> mk_term (Tbinnop (t, dtand, acc)) ) 
      (List.hd terms) (List.tl terms) 

let term_of_post (_, l) = 
  match l with 
  | [(p, t)] -> mk_term (Tcase(mk_tid "result", [p, t])) 
  | _ -> assert false

let mk_equiv t1 t2 =
  let eq = Why3.Dterm.DTiff in 
  mk_term (Tbinnop (t1, eq, t2))


let mk_and t1 t2 =
  let a = Why3.Dterm.DTand in 
  mk_term (Tbinnop (t1, a, t2))

let mk_binder n pty = Loc.dummy_position, Some (mk_id n), false, Some pty



