type _ eff = ..

type ('a,'b) continuation

val perform : 'a eff -> 'a

(** [continue k x] resumes the continuation [k] by passing [x] to [k].
    @raise Invalid_argument if the continuation has already been
    resumed. *)
val continue: ('a, 'b) continuation -> 'a -> 'b

(** [discontinue k e] resumes the continuation [k] by raising the
    exception [e] in [k].
    @raise Invalid_argument if the continuation has already been
    resumed. *)
val discontinue: ('a, 'b) continuation -> exn -> 'b

type ('a,'b) handler =
{ retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option }

val match_with: ('a -> 'b) -> 'a -> ('b,'c) handler -> 'c

type 'a effect_handler =
  { effc: 'b. 'b eff -> (('b, 'a) continuation -> 'a) option }

val try_with: ('a -> 'b) -> 'a -> 'b effect_handler -> 'b
