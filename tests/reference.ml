open Effect
open Effect.Deep
let r : int ref = ref 0
let va : bool ref = ref true

type _ Effect.t += Get : int Effect.t 
type _ Effect.t += Set : int -> unit Effect.t

(*@ protocol Get : 
    ensures reply = !r*)

(*@ protocol Set x :
    ensures !r = x
    modifies r*)


let set n = perform (Set n)
(*@ ensures n = !r
    modifies r*)

let get () = perform Get
(*@ ensures result = !r *)

(*@ predicate fun_post (old_r : int) (r : int) (result : int) =
    result = r * r && r = old_r * 2*)

let some_fun () : int = 
    
    set(get () + get ()); get() * get()
(*@ ensures fun_post (old !r) !r result
    performs Get
    performs Set
    modifies r *)


let f = 
  try_with 
    (fun () -> 
        va := true; 
        let r = some_fun() in 
        (fun (_ : int) : int -> r)) ()
    {effc = 
        (fun (type a) (e : a Effect.t) -> 
            match e with
            |Set n -> 
                Some (fun (k : (a, _) continuation) ->
                    fun (_ : int) : int -> 
                        r:= n;
                        let env : int -> int = continue k () in
                        let ret = env n in 
                 va := false; ret)
            |Get -> 
                Some (fun (k : (a, _) continuation)  ->
                    fun (n : int) : int -> 
                        let env : int -> int = continue k n in
                        let ret = env n in
                 va := false; ret)
            |_ -> None)
    }
    (*@ try_ensures !va 
        try_ensures forall arg state. state._va && state._r = arg -> pre result arg state 
        try_ensures 
            let g = result in 
            forall arg state_old state result.
            post g arg state_old state result -> q (old !r) state._r result
        returns int -> int*)
    (*try_ensures !v
    try_ensures forall arg state. state._v && state._r = arg -> pre result arg state 
    try_ensures r = old !r
    try_ensures let f = result in 
      forall arg state_old state result.
      post f arg state_old state result ->
        fun_post state_old._r state.r result && not state.v*)
