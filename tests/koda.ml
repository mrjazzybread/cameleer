open Effect
open Effect.Deep 

type color = White | Black 

let bits = Array.init 5 (fun _ -> White)

let inc = ref 1

let print_bits () = 
	for i = 0 to Array.length bits - 1 do 
		if bits.(i) = White
			then Printf.printf "white, "
			else Printf.printf "black, "
	done; 
	print_int !inc; 
	inc := !inc + 1; 
	print_newline ()


module Koda_Bin = struct

type forest = E | N of int * forest * forest

let rec enum (bits : color array) (f : forest) (st : unit -> unit) : unit =
  match f with 
  |E -> st ()
  |N(i, l, r) -> 
  	if bits.(i) = White then begin
  		enum bits r st;
  		bits.(i) <- Black;
  		enum bits l (fun () -> enum bits r st) end
  	else if bits.(i) = Black then begin
  		enum bits l (fun () -> enum bits r st);
  		bits.(i) <- White;
  		enum bits r st
  	end
 
(*
effect End : unit

let rec enum_eff (bits : color array) (f : forest) : unit =
  match f with 
  |E -> perform End
  |N(i, l, r) -> 
 	if bits.(i) = White then begin
  		enum bits r st;
  		bits.(i) <- Black;
  		try enum bits l with 
  		|effect End k -> begin enum bits r; continue k () end 
  	else if bits.(i) = Black then begin
  		try enum bits l with 
  		|effect End k -> begin enum bits r; continue k () end;
  		bits.(i) <- White;
  		enum bits r
  	end 
*)



type _ Effect.t += End : unit Effect.t

let rec enum_eff = function 
  |E -> perform End
  |N(i, l, r) ->
		let handler = { 
			effc = fun (type a) (e : a Effect.t) -> 
				match e with 
				|End -> Some (fun (k : (a, _) continuation) -> enum_eff r; continue k())
				|_ -> None
			} in
 	  if bits.(i) = White then begin
  		enum_eff r;
  		bits.(i) <- Black;
  		try_with enum_eff l handler end
  	else if bits.(i) = Black then begin
  		try_with enum_eff l handler;
  		bits.(i) <- White;
  		enum_eff r end 



let forest = 
	N(0, 
		N(1, E, E),
	N(2, 
		N(3, E, 
		N(4, E, E)),
	E))
		
let () = Printf.printf "Koda-Ruskey using Binary Trees\n\n"
let () = try_with (fun () -> enum_eff forest) () 
		 {effc = fun (type a) (e : a Effect.t) -> 
  			match e with 
  			|End -> Some (fun (k : (a, _) continuation) ->
  					print_bits (); continue k ())
  			|_   -> None
		}
	end
(*
module Koda_List = struct

	type tree = Node of int * forest 
	and forest = tree list 

	type color = White | Black 

	let bits = Array.init 5 (fun _ -> White)

	let inc = ref 1

	let print_bits () = 
		for i = 0 to Array.length bits - 1 do 
			if bits.(i) = White
				then Printf.printf "white, "
				else Printf.printf "black, "
		done; 
		print_int !inc; 
		inc := !inc + 1; 
		print_newline ()

	type _ Effect.t += End : unit Effect.t

	(*
	let rec enum_forest (f : forest) (k : unit -> unit) = match f with 
		|[] -> k ()
		|t :: f -> enum_tree (fun () -> enum_forest k f) t 
		and enum_tree k (Node(i, f)) = 
			if bits.(i) = White 
				then begin k(); bits.(i) <- Black; enum_forest k f end 
				else begin enum_forest k f; bits.(i) <- White; k() end 

	let rec enum_forest (f : forest) (k : unit -> unit) = match f with 
	|[] -> k ()
	|t :: f -> let k = (fun () -> enum_forest k f) in 
			if bits.(i) = White 
				then begin k (); bits.(i) <- Black; enum_forest k f end 
				else begin enum_forest k f; bits.(i) <- White; k() end 

	
let rec enum_eff (f : forest) : unit =
  match f with 
  |E -> perform End
  |Node(i, ft) :: f-> 
 	if bits.(i) = White then begin 
				enum_eff f; 
				bits.(i) <- Black; 
				try enum_eff ft handler with 
				|effect End k -> enum_eff f 
		else begin 
				try enum_eff ft handler with 
				|effect End k -> enum_eff f; 
				bits.(i) <- White; 
				enum_eff f end 
		*)

	let rec enum_eff = function
	|[] -> perform End 
	|Node(i, ft) :: f -> 
		let handler = { 
			effc = fun (type a) (e : a Effect.t) -> 
				match e with 
				|End -> Some (fun (k : (a, _) continuation) -> enum_eff f; continue k())
				|_ -> None
			} in 
		if bits.(i) = White then begin 
				enum_eff f; 
				bits.(i) <- Black; 
				try_with enum_eff ft handler end 
		else begin 
				try_with enum_eff ft handler; 
				bits.(i) <- White; 
				enum_eff f end 
			
	let main f = 
		try_with (fun () -> enum_eff f) () { 
								effc = fun (type a) (e : a Effect.t) -> 
									match e with 
									|End -> Some (fun (k : (a, _) continuation) -> print_bits (); continue k ())
									|_ -> None
								} 

	let forest = [Node(0, [Node(1, [])]); Node(2, [Node(3, []); Node(4, [])])]

	let () = Printf.printf "Koda-Ruskey using Lists of trees\n\n"
	let () = main forest

	let rec enum_forest (k : unit -> unit) (f : forest) = match f with 
	|[] -> k ()
	|t :: f -> let k = (fun () -> enum_forest k f) in 
		let Node(i, f) = t in
		if bits.(i) = White 
			then begin k (); bits.(i) <- Black; enum_forest k f end 
			else begin enum_forest k f; bits.(i) <- White; k() end 

let () = for i = 0 to 4 do Array.set bits i White done

let () = Printf.printf "Koda-Ruskey using Lists of trees with no effects\n\n"
let () = inc := 1

let () = enum_forest print_bits forest

end
*)
