
module Map = Map.Make(String)
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
