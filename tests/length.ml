
let rec length_cps l (k : int -> 'a) : 'a =
  match l with
  | [] -> k 0
  | _::t -> 
    length_cps t 
    (fun [@gospel {|ensures post k (r + 1) () () result|}] (r : int) : 'a -> k (r + 1))
(*@ variant l
    requires forall arg state. pre k arg state
    ensures post k (length l) () () result*)


let length_direct l  =
  length_cps l (fun [@gospel {|ensures x = result|}] (x : 'a) : 'a -> x)