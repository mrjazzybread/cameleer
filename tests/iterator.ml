open Effect
open Effect.Deep

let l : (int list) ref = ref []
let v : (unit -> int option) ref = ref (fun () : int option -> None)

let gen : (unit -> int option) ref = ref (fun () : int option -> None)

type _ Effect.t += Yield : int -> unit Effect.t 

(*@ predicate next (prev : int list) (next : int)*)
(*@ predicate complete (l : int list)*)
(*@ predicate iter_inv (s_old : state) (s : state) (result : int option)*)

(*@
axiom iter_inv1 :
  forall state_old state. 
  complete state._l && state = state_old <-> iter_inv state_old state None
*)

(*@  
axiom iter_inv2 :
  forall state_old state r. (
    next state_old._l r && state._l = r::state_old._l && state._v = state._gen &&
      forall state_old1 state1 result. 
      (post state._gen () state_old1 state1 result -> iter_inv state_old1 state1 result) &&
      (state_old1._v = state._gen -> pre state._gen () state_old1)
      
      ) <-> iter_inv state_old state (Some r)
*)

(*@ protocol Yield x :  
    requires next !l x
    ensures !l = x::(old !l)
    modifies l, v, gen*)

let iter (f : int -> unit) : unit = perform (Yield 0); assert false
(*@ requires forall arg s. next s._l arg -> pre f arg s
    ensures complete !l
    performs Yield*)
    
let a = 
  try_with 
  (fun () -> 
    iter 
      (fun [@gospel {|
            requires next !l x
            performs Yield|}] 
            (x : int) : unit -> perform (Yield x));
    
    gen := 
      (fun [@gospel {|ensures iter_inv {_l = old !l; _v = old !v; _gen = old !gen} {_l = !l; _v = !v; _gen = !gen} result|}] 
        () : int option -> None) ; v := !gen) ()
  {effc = 
    fun (type a) (e : a Effect.t) ->
      match e with 
      | Yield x -> Some
        (fun (k : (a, _ ) continuation) -> 
            gen := 
              (fun [@gospel {|
              ensures iter_inv {_l = old !l; _v = old !v; _gen = old !gen} {_l = !l; _v = !v; _gen = !gen}  result|}] 
              () : int option -> l := x::!l;  continue k (); Some x);
              v := !gen )
            
      |_ -> None
  }
  (*@ try_ensures !v = !gen
      try_ensures forall arg s. s._v = !gen -> pre !gen arg s
      try_ensures  
        forall s_old s result. post !gen () s_old s result -> iter_inv s_old s result*)