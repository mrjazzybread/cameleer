(*type 'a eff = ..*)

type _ eff += Div_by_zero : int eff

type exp = Const of int | Div of exp * exp

(*@function eval_ind (exp : exp) : int =
match exp with
|Const n -> n
|Div exp1 exp2 -> div (eval_ind exp1) (eval_ind exp2)
 *)

(*@predicate right_zero (e : exp) =
   match e with 
   |Const _ -> false
   |Div _ r -> eval_ind r = 0 *)

let curr_exp : exp ref = ref (Const 0) 

(*@ protocol Div_by_zero : 
   requires right_zero (!curr_exp)
   ensures !curr_exp = Const reply
   modifies curr_exp
  *)

let rec eval e = 
   match e with 
   |Const n -> curr_exp:=e; n 
   |Div(e1, e2) -> 
      let eval_l = eval e1 in 
      let l = !curr_exp in 
      let eval_r = eval e2 in 
      curr_exp:= Div(l, !curr_exp);
      if eval_r = 0 
         then perform Div_by_zero
         else eval_l / eval_r
(*@
   ensures eval_ind (!curr_exp) = result
   variant e
*)

