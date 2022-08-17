type _ t = ..

module Deep : sig

type ('a,'b) continuation
type ('a,'b) handler 

  type 'a effect_handler =
  { effc: 'b. 'b t -> (('b, 'a) continuation -> 'a) option }

val perform : 'a t -> 'a

val continue : (('a, 'b) continuation) -> 'a -> 'b

val try_with : ('a -> 'b) -> 'a -> 'b effect_handler -> 'b

end