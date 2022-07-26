effect Yield : int -> unit

let gen = ref (fun () -> None) 
   


let mk_gen it =
  try it (fun x -> perform (Yield x)); gen := (fun () -> None) with 
  |effect (Yield x) k -> gen := (fun () -> continue k (); Some x) 


let () = mk_gen (fun f -> List.iter f [1;2;3;4])

let a = Option.get (!gen())
let b = Option.get (!gen())
let c = Option.get (!gen())

let () = Printf.printf "%d %d %d\n" a b c