open Effect
open Effect.Deep

type exp = Const of int | Div of exp * exp
let v0 : int ref = ref 0

type _ Effect.t += Div_by_zero : int Effect.t


(*@ function eval_ind (exp : exp) (v0 : int) : int =
match exp with
|Const n -> n
|Div exp1 exp2 -> 
   if eval_ind exp2 v0 = 0 
      then v0 
      else div (eval_ind exp1 v0) (eval_ind exp2 v0)  
*)

(*@ protocol Div_by_zero : 
    ensures reply = !v0
  *)

let rec eval (e : exp) : int = 
   match e with 
   |Const n -> n 
   |Div(e1, e2) -> 
      let eval_l = eval e1 in 
      let eval_r = eval e2 in 
      if eval_r = 0 
         then perform Div_by_zero
         else eval_l / eval_r
(*@
   ensures eval_ind e !v0 = result
   performs Div_by_zero 
   variant e
*)

(* try v0 := 1000; eval e with 
   |effect Div_by_zero k -> continue k 1000 *)

let main exp = 
   try_with (fun e -> v0 := 1000; eval e) exp
   { effc = fun (type a) (e : a Effect.t)  ->
     match e with 
     |Div_by_zero -> Some (fun (k : (a,_) continuation) -> 
      continue k 1000) 
     |_ -> None } 
(*@try_ensures eval_ind exp 1000 = result 
      returns int *)