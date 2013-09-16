(* Equality operators *)

val ( = )
  : ('x * 'x) -> bool
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

(* Integer operators *)

val ( + )
  : (int * int) -> int
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( - )
  : (int * int) -> int
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( * )
  : (int * int) -> int
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( / )
  : (int * int) -> int
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( <= )
  : (int * int) -> bool
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( < )
  : (int * int) -> bool
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( >= )
  : (int * int) -> bool
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( > )
  : (int * int) -> bool
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

(* Floating-point operators *)

val ( +. )
  : (float * float) -> float
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( -. )
  : (float * float) -> float
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( *. )
  : (float * float) -> float
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

val ( /. )
  : (float * float) -> float
  is ('c * 'c) -> 'c
  :: ('a * 'a) -> 'a

(* Internal operators *)

val box
  : 'x -> 'x boxed
  is 'c -> 'c
  :: 'b -> 'b

val unbox
  : 'x boxed -> 'x
  is 'c -> 'c
  :: 'b -> 'b