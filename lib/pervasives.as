(* Equality operators *)

val ( = )
  : ('x * 'x) -> bool
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

(* Integer operators *)

val ( + )
  : (int * int) -> int
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( - )
  : (int * int) -> int
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( * )
  : (int * int) -> int
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( / )
  : (int * int) -> int
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

(* Floating-point operators *)

val ( +. )
  : (float * float) -> float
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( -. )
  : (float * float) -> float
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( *. )
  : (float * float) -> float
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a

val ( /. )
  : (float * float) -> float
  is ('s * 's) -> 's
  :: ('a * 'a) -> 'a
