
type __ = Obj.t

val xorb : bool -> bool -> bool

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> nat

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type int =
| Pos of uint
| Neg of uint

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : int -> int

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint
 end

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3

module type DecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type DecidableTypeOrig =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module type MiniDecidableType =
 sig
  type t

  val eq_dec : t -> t -> bool
 end

module Make_UDT :
 functor (M:MiniDecidableType) ->
 sig
  type t = M.t

  val eq_dec : t -> t -> bool
 end

module Nat :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : int -> nat option

  val to_int : nat -> int

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> bool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> bool

    val min_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> bool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> bool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end

val le_lt_dec : nat -> nat -> bool

val le_gt_dec : nat -> nat -> bool

val le_dec : nat -> nat -> bool

val lt_dec : nat -> nat -> bool

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val string_dec : char list -> char list -> bool

module type Coq_DecidableType =
 DecidableTypeOrig

module KeyDecidableType :
 functor (D:Coq_DecidableType) ->
 sig
 end

module Raw :
 functor (X:Coq_DecidableType) ->
 sig
  module PX :
   sig
   end

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val mem : key -> 'a1 t -> bool

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

  val coq_R_mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
    coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
    coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
    -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
    'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
    -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add ->
    'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
    -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
    -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove ->
    'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove ->
    'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
    -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2
    -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2
    -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3
    -> 'a3) -> 'a1 t -> 'a2 -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3
    -> 'a3) -> 'a1 t -> 'a2 -> 'a3

  val coq_R_fold_correct : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

  val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

  val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val fold_right_pair : ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

  val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

  val at_least_left : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_right : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val at_least_one : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

  val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

  val map2 : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3) list

  val at_least_one_then_f : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option
 end

module Make :
 functor (X:Coq_DecidableType) ->
 sig
  module Raw :
   sig
    module PX :
     sig
     end

    type key = X.t

    type 'elt t = (X.t * 'elt) list

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val mem : key -> 'a1 t -> bool

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt t
    | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

    val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

    val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

    val find : key -> 'a1 t -> 'a1 option

    type 'elt coq_R_find =
    | R_find_0 of 'elt t
    | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
      coq_R_find -> 'a2

    val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
      coq_R_find -> 'a2

    val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    type 'elt coq_R_add =
    | R_add_0 of 'elt t
    | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
      -> 'a2

    val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t
      -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

    val remove : key -> 'a1 t -> 'a1 t

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt t
    | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_remove

    val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      -> 'a2

    val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove
      -> 'a2

    val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1
      -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

    val elements : 'a1 t -> 'a1 t

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    type ('elt, 'a) coq_R_fold =
    | R_fold_0 of 'elt t * 'a
    | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a * ('elt, 'a) coq_R_fold

    val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2
      -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2
      -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3
      -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3
      -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val coq_R_fold_correct : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

    val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

    val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val fold_right_pair : ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

    val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val at_least_left : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_right : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_one : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

    val map2 : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3) list

    val at_least_one_then_f : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option
   end

  module E :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool
   end

  type key = E.t

  type 'elt slist = 'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  val this : 'a1 slist -> 'a1 Raw.t

  type 'elt t = 'elt slist

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

module Nat_as_OT :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : int -> nat option

  val to_int : nat -> int

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> bool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> bool

    val min_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> bool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> bool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end

module MakeRaw :
 functor (X:DecidableType) ->
 sig
  type elt = X.t

  type t = elt list

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val union : t -> t -> t

  val diff : t -> t -> t

  val inter : t -> t -> t

  val subset : t -> t -> bool

  val equal : t -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val isok : elt list -> bool
 end

module Coq_Make :
 functor (X:DecidableType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool
 end

type terminal = char list

type nonterminal = nat

type symbol =
| T of terminal
| NT of nonterminal

module NT_as_DT :
 sig
  type t = nat

  val zero : nat

  val one : nat

  val two : nat

  val succ : nat -> nat

  val pred : nat -> nat

  val add : nat -> nat -> nat

  val double : nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val compare : nat -> nat -> comparison

  val max : nat -> nat -> nat

  val min : nat -> nat -> nat

  val even : nat -> bool

  val odd : nat -> bool

  val pow : nat -> nat -> nat

  val tail_add : nat -> nat -> nat

  val tail_addmul : nat -> nat -> nat -> nat

  val tail_mul : nat -> nat -> nat

  val of_uint_acc : uint -> nat -> nat

  val of_uint : uint -> nat

  val to_little_uint : nat -> uint -> uint

  val to_uint : nat -> uint

  val of_int : int -> nat option

  val to_int : nat -> int

  val divmod : nat -> nat -> nat -> nat -> nat * nat

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val gcd : nat -> nat -> nat

  val square : nat -> nat

  val sqrt_iter : nat -> nat -> nat -> nat -> nat

  val sqrt : nat -> nat

  val log2_iter : nat -> nat -> nat -> nat -> nat

  val log2 : nat -> nat

  val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : nat -> nat

  val testbit : nat -> nat -> bool

  val shiftl : nat -> nat -> nat

  val shiftr : nat -> nat -> nat

  val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat

  val coq_land : nat -> nat -> nat

  val coq_lor : nat -> nat -> nat

  val ldiff : nat -> nat -> nat

  val coq_lxor : nat -> nat -> nat

  val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1

  val eq_dec : nat -> nat -> bool

  val leb_spec0 : nat -> nat -> reflect

  val ltb_spec0 : nat -> nat -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val max_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : nat -> nat -> bool

    val min_case_strong : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

    val min_case : nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : nat -> nat -> bool
   end

  val max_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val max_dec : nat -> nat -> bool

  val min_case_strong : nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1

  val min_dec : nat -> nat -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : nat -> nat

  val log2_up : nat -> nat

  module Private_NZDiv :
   sig
   end

  val lcm : nat -> nat -> nat

  val eqb_spec : nat -> nat -> reflect

  val b2n : bool -> nat

  val setbit : nat -> nat -> nat

  val clearbit : nat -> nat -> nat

  val ones : nat -> nat

  val lnot : nat -> nat -> nat
 end

module NtSet :
 sig
  module Raw :
   sig
    type elt = nat

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> nat

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = nat

    val eq_dec : nat -> nat -> bool
   end

  type elt = nat

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> nat

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool
 end

type tree =
| Leaf of terminal
| Node of nonterminal * tree list

type lookahead =
| LA of terminal
| EOF

type pt_key = nonterminal * lookahead

val pt_key_eq_dec : pt_key -> pt_key -> bool

module MDT_PtKey :
 sig
  type t = pt_key

  val eq_dec : pt_key -> pt_key -> bool
 end

module PtKey_as_DT :
 sig
  type t = pt_key

  val eq_dec : pt_key -> pt_key -> bool
 end

module ParseTable :
 sig
  module Raw :
   sig
    module PX :
     sig
     end

    type key = pt_key

    type 'elt t = (pt_key * 'elt) list

    val empty : 'a1 t

    val is_empty : 'a1 t -> bool

    val mem : key -> 'a1 t -> bool

    type 'elt coq_R_mem =
    | R_mem_0 of 'elt t
    | R_mem_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
    | R_mem_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * bool * 'elt coq_R_mem

    val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
      coq_R_mem -> 'a2

    val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
      coq_R_mem -> 'a2

    val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

    val find : key -> 'a1 t -> 'a1 option

    type 'elt coq_R_find =
    | R_find_0 of 'elt t
    | R_find_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
    | R_find_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt option * 'elt coq_R_find

    val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      option -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      option -> 'a1 coq_R_find -> 'a2

    val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    type 'elt coq_R_add =
    | R_add_0 of 'elt t
    | R_add_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
    | R_add_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
      -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
      -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_add -> 'a2

    val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
      -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t
      -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

    val remove : key -> 'a1 t -> 'a1 t

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt t
    | R_remove_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
    | R_remove_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t * 'elt coq_R_remove

    val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_remove -> 'a2

    val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_remove -> 'a2

    val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

    val elements : 'a1 t -> 'a1 t

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    type ('elt, 'a) coq_R_fold =
    | R_fold_0 of 'elt t * 'a
    | R_fold_1 of 'elt t * 'a * pt_key * 'elt * (pt_key * 'elt) list * 'a * ('elt, 'a) coq_R_fold

    val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __
      -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __
      -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __
      -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __
      -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val coq_R_fold_correct : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

    val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

    val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val fold_right_pair : ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

    val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val at_least_left : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_right : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_one : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

    val map2 : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3) list

    val at_least_one_then_f : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3 option
   end

  module E :
   sig
    type t = pt_key

    val eq_dec : pt_key -> pt_key -> bool
   end

  type key = pt_key

  type 'elt slist = 'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  val this : 'a1 slist -> 'a1 Raw.t

  type 'elt t = 'elt slist

  val empty : 'a1 t

  val is_empty : 'a1 t -> bool

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  val find : key -> 'a1 t -> 'a1 option

  val remove : key -> 'a1 t -> 'a1 t

  val mem : key -> 'a1 t -> bool

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map2 : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end

type parse_table = symbol list ParseTable.t

val pt_lookup : nonterminal -> lookahead -> parse_table -> symbol list option

val peek : terminal list -> lookahead

val ptlk_dec : nonterminal -> lookahead -> parse_table -> (__, symbol list) sum

type parse_failure =
| Reject of char list * char list list
| LeftRec of nonterminal * NtSet.t * char list list

val mem_dec : nonterminal -> NtSet.t -> bool

val parse_nf : parse_table -> symbol -> char list list -> NtSet.t -> (parse_failure, tree * char list list) sum

val parseForest_nf : parse_table -> symbol list -> char list list -> NtSet.t -> (parse_failure, tree list * char list list) sum

val parse_wrapper : parse_table -> symbol -> char list list -> NtSet.t -> (parse_failure, tree * char list list) sum
