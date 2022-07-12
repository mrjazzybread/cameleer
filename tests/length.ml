
let rec length_cps l (k : int -> 'a) : 'a =
  match l with
  | [] -> assert false(*k 0*)
  | _::t -> assert false(*length_cps t (fun r -> k (r +1))*)

