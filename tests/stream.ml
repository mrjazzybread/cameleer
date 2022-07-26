open Dummy_effect

type _ eff += Yield : int -> unit eff

let () = Printf.printf "Wow\n"

let join_stream s1 s2 =
  let start s =
    try_with (fun () -> s1 (fun x -> perform (Yield x)); None) () 
    { 
      effc = fun (type a) (e : a eff) ->
        match e with 
        |Yield x -> Some (fun (k : (a, _) continuation) -> 
          let f = fun () -> continue k () in 
          Some (x, ))
        |_ -> None
    }  in assert false

