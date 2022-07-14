let f (x : int) : (int -> int -> int) * int = (fun (y : int) (z : int) : int -> y +x + z), x
(*@ ensures 
    match result with |f, _ -> 
      (no_pre f && forall arg old_state state result. post f arg old_state state result -> no_pre result) *)

let id x = x
(* ensures x = result *)
let l = (match f 4 with |x, _ -> x ) 4 5