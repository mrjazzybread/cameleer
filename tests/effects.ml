(*type 'a eff = ..*)

type _ eff += Div_by_zero : int -> int eff

(*@ protocol Div_by_zero x : 
   requires false
   ensures true*)