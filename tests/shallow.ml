open Effect
open Effect.Shallow

type _ Effect.t += E : unit Effect.t 
type _ Effect.t += Wildcard : unit Effect.t

let a = ref 0

let rec deep: 'a. (('a, _) continuation) -> 'a -> _ = fun k arg ->   
  continue_with k arg {
    retc = (fun x -> x);
    exnc = (fun _ -> assert false);
    effc = 
      (fun (type a) (e : a Effect.t) -> 
        match e with 
        |E -> (Some (fun (k : (a, _) continuation) -> 
          Printf.printf "Handled %d!\n" !a; 
          deep k ()))
        |_ -> Nonewhyf
      )
  }
(*@ requires valid k 
    requires pre k arg
    requires k performs E
    ensures post k () result*)

let rec deep k arg = 
  resume k arg with 
  |effect E k -> deep k () 

let handle f arg = deep (fiber f) arg
(*@ requires pre f arg
    requires f performs E
    ensures post f arg result *)

let () = handle (fun () -> for i = 0 to 10 do a:=i; perform E done) ()
