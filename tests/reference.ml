
let r : int ref = ref 0

type _ eff += Get : int eff 
type _ eff += Set : int -> unit eff

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

(*@ predicate fun_post1 (old_r : int) (r : int) (result : int) =
    result = r * r && r = old_r * 2*)

let some_fun () : int = set(get () + get ()); get() * get()
(*@ ensures fun_post1 (old !r) !r result
    performs Get
    performs Set
    modifies r *)
(*
let f = 
  match v:= true; some_fun () with
  |n -> fun (_ : int) : int -> n
  |effect Get k -> fun (n : int) : int -> (let ret = continue k n n in v:=false; ret) 
  |effect (Set n) k -> fun (_ : int) : int -> (let ret = continue k () n in v:=false; ret) 
(*  try_ensures !v
    try_ensures forall arg state. state._v && state._r = arg -> pre result arg state 
    try_ensures r = old !r
    try_ensures let f = result in 
      forall arg state_old state result.
      post f arg state_old state result ->
        fun_post state_old._r state.r result && not state.v*)


let () = Printf.printf "%d" (f 2)
*)