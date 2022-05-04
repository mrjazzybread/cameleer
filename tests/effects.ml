(*type 'a eff = ..*)

type _ eff += Div_by_zero : int * int -> int eff

(*@ protocol Div_by_zero x y : 
   requires false
   ensures true*)