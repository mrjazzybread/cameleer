(*type 'a eff = ..*)

type _ eff += Div_by_zero : int eff

type exp = Const of int | Div of exp * exp


let curr_exp = ref (Const 0) 

(*@ protocol Div_by_zero : 
   requires false
   ensures true*)

