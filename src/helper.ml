open Why3
open Ptree

let dummy_loc = Loc.dummy_position
let mk_term ?(term_loc = dummy_loc) term_desc = { term_desc; term_loc }

let mk_id ?(id_ats = []) ?(id_loc = dummy_loc) id_str =
  { id_str; id_ats; id_loc }

let mk_expr ?(expr_loc = dummy_loc) expr_desc = { expr_desc; expr_loc }

let mk_tid s = 
  mk_term (Tident (Qident (mk_id s)))

let mk_eid s =
  mk_expr (Eident (Qident (mk_id s)))
let pre = mk_tid "pre"

let post = mk_tid "post"