type _ eff += Div_by_zero : int eff

(*@ protocol Div_by_zero : 
   requires false
   ensures true*)