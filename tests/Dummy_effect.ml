type _ eff = ..
type ('a,'b) continuation = 'a * 'b
type ('a,'b) handler =
{ retc: 'a -> 'b;
  exnc: exn -> 'b;
  effc: 'c.'c eff -> (('c,'b) continuation -> 'b) option }

  type 'a effect_handler =
  { effc: 'b. 'b eff -> (('b, 'a) continuation -> 'a) option }

let perform _ = failwith ""

let continue _ _ = failwith ""

let discontinue _ _ = failwith ""

let match_with _ _ _ = failwith ""

let try_with _ _ _ = failwith ""
