open Gospel
open Odecl

val eff_name : string

val map_effect : string -> Why3.Ptree.pty -> unit 
val map_ref_type : string -> Why3.Ptree.pty -> unit
val s_structure : info -> Uast.s_structure -> odecl list
val s_signature : info -> Uast.s_signature -> odecl list
