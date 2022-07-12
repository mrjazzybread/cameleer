
let rec length_cps l (k : int -> 'a) : 'a =
  match l with
  | [] -> k 0
  | _::t -> assert false(*length_cps t (fun r -> k (r +1))*)

