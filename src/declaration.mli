open Gospel
open Odecl

(** name of the type of effects in the WhyML translation*)
val eff_name : string

(** Maps the name of an effect with its return type*)
val map_effect : string -> Why3.Ptree.pty -> unit 

(** maps the name of an OCaml reference to the variable type it holds *)
val map_ref_type : string -> Why3.Ptree.pty -> unit



val s_structure : info -> Uast.s_structure -> odecl list
val s_signature : info -> Uast.s_signature -> odecl list

