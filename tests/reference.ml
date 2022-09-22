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


let set (n : int) : unit = perform (Set n)
(*@ ensures n = !r
    performs Set*)


let get () : int = perform Get
(*@ ensures result = !r
    performs Get *)

(*@ predicate fun_post (old_r : int) (r : int) (result : int) =
    result = r * r && r = old_r * 2*)


let some_fun () : int = 
    set(get () + get ()); get() * get()
(*@ ensures fun_post (old !r) !r result
    performs Get
    performs Set*)



  let f : int -> int = 
  try_with 
    (fun () ->  
        let ret = some_fun() in 
        let final_r = !r in 
        (fun [@gospel {| ensures fun_post init_state._r final_r result && !r = final_r|}] (_ : int) : int -> r:= final_r; ret)) ()
    {effc = 
        (fun (type a) (e : a Effect.t) -> 
            match e with
            |Set n -> 
                Some (fun (k : (a, _) continuation) ->
                    fun 
                    [@gospel {| requires !va
                        ensures fun_post init_state._r !r result |}]
                    (_ : int) : int -> 
                        r := n;
                        let env : int -> int = continue k () in
                        env n)
            |Get -> 
                Some (fun (k : (a, _) continuation)  ->
                    fun 
                    [@gospel {|
                        requires !r = n && !va
                        ensures fun_post init_state._r !r result
                    |}]
                    (n : int) : int -> 
                        let env : int -> int = continue k n in
                        env n)
            |_ -> None)
    }
    (*@
        try_ensures forall arg state. 
            state._va && state._r = arg -> pre result arg state
        try_ensures let g = result in  
            forall arg state_old state result. 
            post g arg state_old state result ->
                fun_post (old !r) state._r result
        returns int -> int *)