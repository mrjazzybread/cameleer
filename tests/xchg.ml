open Effect
open Effect.Deep

let p : int ref = ref 0

type 'a Effect.t += XCHG : int -> int Effect.t

(*@ protocol XCHG x :
    ensures !p = x && reply = old !p
    modifies p *)

let xchg (x : int) : int =
  perform (XCHG x)
(*@ ensures !p = x && result = old !p
    performs XCHG *)

let server =
  try_with (fun x -> xchg x) 3
    {effc =
       (fun (type a) (e : a Effect.t) ->
          match e with
          |XCHG n -> (Some (fun (k : (a, _) continuation) ->
              let old_p = !p in
              p := n;
              continue k old_p))
          |_ -> None)}
(*@ try_ensures !p = 3 && result = old !p
    returns int*)
