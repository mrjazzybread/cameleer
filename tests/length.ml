
let rec length_cps l (k : int -> 'a) : 'a =
  match l with
  | [] -> k 0
  | _::t -> length_cps t (fun (r : int) : 'a -> k (r +1))
(*@ requires no_pre k
    ensures post k (length l) () () result*)

let length_direct l =
  length_cps l (assert false) (fun (x : 'a) : 'a -> x)

