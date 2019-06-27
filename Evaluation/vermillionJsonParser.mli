
type __ = Obj.t

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

val app : 'a1 list -> 'a1 list -> 'a1 list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



val add : nat -> nat -> nat

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

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val append : char list -> char list -> char list

module type Coq_DecidableType =
 DecidableTypeOrig

module KeyDecidableType :
 functor (D:Coq_DecidableType) ->
 sig
 end

module WFacts_fun :
 functor (E:Coq_DecidableType) ->
 functor (M:sig
  type key = E.t

  type 'x t

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
 end) ->
 sig
  val eqb : E.t -> E.t -> bool

  val coq_In_dec : 'a1 M.t -> M.key -> bool
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
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
    'a2

  val coq_R_mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
    'a2

  val mem_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val mem_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

  val find : key -> 'a1 t -> 'a1 option

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
     * 'elt coq_R_find

  val coq_R_find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
    coq_R_find -> 'a2

  val coq_R_find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
    coq_R_find -> 'a2

  val find_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val find_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

  val add : key -> 'a1 -> 'a1 t -> 'a1 t

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_add

  val coq_R_add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
    __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_add -> 'a2

  val coq_R_add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
    __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_add -> 'a2

  val add_rect :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
    __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val add_rec :
    key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list
    -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ ->
    __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

  val remove : key -> 'a1 t -> 'a1 t

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
     * 'elt coq_R_remove

  val coq_R_remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_remove -> 'a2

  val coq_R_remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
    coq_R_remove -> 'a2

  val remove_rect :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val remove_rec :
    key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
    -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
    __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

  val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

  val elements : 'a1 t -> 'a1 t

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
     * ('elt, 'a) coq_R_fold

  val coq_R_fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 ->
    'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val coq_R_fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 ->
    'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

  val fold_rect :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

  val fold_rec :
    (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
    X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

  val coq_R_fold_correct :
    (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

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

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3) list

  val at_least_one_then_f :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3
    option
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
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
      coq_R_mem -> 'a2

    val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
      coq_R_mem -> 'a2

    val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

    val find : key -> 'a1 t -> 'a1 option

    type 'elt coq_R_find =
    | R_find_0 of 'elt t
    | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt option
       * 'elt coq_R_find

    val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option
      -> 'a1 coq_R_find -> 'a2

    val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option
      -> 'a1 coq_R_find -> 'a2

    val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

    val add : key -> 'a1 -> 'a1 t -> 'a1 t

    type 'elt coq_R_add =
    | R_add_0 of 'elt t
    | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t * 'elt coq_R_add

    val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
      __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_add -> 'a2

    val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
      __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
      'a1 coq_R_add -> 'a2

    val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
      __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1)
      list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list ->
      __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

    val remove : key -> 'a1 t -> 'a1 t

    type 'elt coq_R_remove =
    | R_remove_0 of 'elt t
    | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
    | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 'elt t
       * 'elt coq_R_remove

    val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
      coq_R_remove -> 'a2

    val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
      coq_R_remove -> 'a2

    val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __
      -> __ -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __
      -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

    val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

    val elements : 'a1 t -> 'a1 t

    val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

    type ('elt, 'a) coq_R_fold =
    | R_fold_0 of 'elt t * 'a
    | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list * 'a
       * ('elt, 'a) coq_R_fold

    val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3
      -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3
      -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3

    val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t -> 'a2 ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

    val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

    val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

    val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

    val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

    val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

    val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

    val at_least_left : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_right :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val at_least_one : 'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

    val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

    val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3) list

    val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option -> 'a3
      option
   end

  module E :
   sig
    type t = X.t

    val eq_dec : t -> t -> bool
   end

  type key = E.t

  type 'elt slist =
    'elt Raw.t
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

module type WSets =
 sig
  module E :
   DecidableType

  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end

module WFactsOn :
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 sig
  val eqb : E.t -> E.t -> bool
 end

module WDecideOn :
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 sig
  module F :
   sig
    val eqb : E.t -> E.t -> bool
   end

  module MSetLogicalFacts :
   sig
   end

  module MSetDecideAuxiliary :
   sig
   end

  module MSetDecideTestCases :
   sig
   end
 end

module WPropertiesOn :
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : E.t -> E.t -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb : E.t -> E.t -> bool
   end

  val coq_In_dec : M.elt -> M.t -> bool

  val of_list : M.elt list -> M.t

  val to_list : M.t -> M.elt list

  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
    M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2

  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
    (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t ->
    'a1

  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
    -> M.t -> 'a1

  val cardinal_inv_2 : M.t -> nat -> M.elt

  val cardinal_inv_2b : M.t -> M.elt
 end

module WProperties :
 functor (M:WSets) ->
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : M.E.t -> M.E.t -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb : M.E.t -> M.E.t -> bool
   end

  val coq_In_dec : M.elt -> M.t -> bool

  val of_list : M.elt list -> M.t

  val to_list : M.t -> M.elt list

  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
    M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2

  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
    (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t ->
    'a1

  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
    -> M.t -> 'a1

  val cardinal_inv_2 : M.t -> nat -> M.elt

  val cardinal_inv_2b : M.t -> M.elt
 end

module Properties :
 functor (M:WSets) ->
 sig
  module Dec :
   sig
    module F :
     sig
      val eqb : M.E.t -> M.E.t -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  module FM :
   sig
    val eqb : M.E.t -> M.E.t -> bool
   end

  val coq_In_dec : M.elt -> M.t -> bool

  val of_list : M.elt list -> M.t

  val to_list : M.t -> M.elt list

  val fold_rec :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
    M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_bis :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
    -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

  val fold_rec_nodep :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
    'a2) -> 'a2

  val fold_rec_weak :
    (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2
    -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

  val fold_rel :
    (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
    (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

  val set_induction :
    (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t ->
    'a1

  val set_induction_bis :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
    -> M.t -> 'a1

  val cardinal_inv_2 : M.t -> nat -> M.elt

  val cardinal_inv_2b : M.t -> M.elt
 end

module WEqPropertiesOn :
 functor (E:DecidableType) ->
 functor (M:sig
  type elt = E.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> nat

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool
 end) ->
 sig
  module MP :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : E.t -> E.t -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : E.t -> E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> bool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
      M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
      'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
      (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t
      -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
      -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  val choose_mem_3 : M.t -> M.elt

  val set_rec :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __ -> 'a1 -> 'a1) -> 'a1
    -> M.t -> 'a1

  val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val sum : (M.elt -> nat) -> M.t -> nat
 end

module WEqProperties :
 functor (M:WSets) ->
 sig
  module MP :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : M.E.t -> M.E.t -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : M.E.t -> M.E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> bool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
      M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
      'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
      (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t
      -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
      -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  val choose_mem_3 : M.t -> M.elt

  val set_rec :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __ -> 'a1 -> 'a1) -> 'a1
    -> M.t -> 'a1

  val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val sum : (M.elt -> nat) -> M.t -> nat
 end

module EqProperties :
 functor (M:WSets) ->
 sig
  module MP :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : M.E.t -> M.E.t -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : M.E.t -> M.E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> bool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt -> 'a1 ->
      M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
      'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t -> 'a3 ->
      (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1) -> M.t
      -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1 -> 'a1)
      -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> nat -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
   end

  val choose_mem_3 : M.t -> M.elt

  val set_rec :
    (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __ -> 'a1 -> 'a1) -> 'a1
    -> M.t -> 'a1

  val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt

  val sum : (M.elt -> nat) -> M.t -> nat
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

module type SYMBOL_TYPES =
 sig
  type terminal

  type nonterminal

  val t_eq_dec : terminal -> terminal -> bool

  val nt_eq_dec : nonterminal -> nonterminal -> bool

  val show_t : terminal -> char list

  val show_nt : nonterminal -> char list

  type t_semty

  type nt_semty
 end

module DefsFn :
 functor (Ty:SYMBOL_TYPES) ->
 sig
  type symbol =
  | T of Ty.terminal
  | NT of Ty.nonterminal

  val symbol_rect : (Ty.terminal -> 'a1) -> (Ty.nonterminal -> 'a1) -> symbol -> 'a1

  val symbol_rec : (Ty.terminal -> 'a1) -> (Ty.nonterminal -> 'a1) -> symbol -> 'a1

  type production = Ty.nonterminal * symbol list

  val symbol_eq_dec : symbol -> symbol -> bool

  val show_symbol : symbol -> char list

  val prependToAll : char list -> char list list -> char list

  val intersperse : char list -> char list list -> char list

  val show_rhs : symbol list -> char list

  val show_prod : production -> char list

  type symbol_semty = __

  type tuple = __

  type rhs_semty = tuple

  type action_ty = __

  type xprod = (production, action_ty) sigT

  type token = (Ty.terminal, Ty.t_semty) sigT

  type grammar = { start : Ty.nonterminal; prods : xprod list }

  val start : grammar -> Ty.nonterminal

  val prods : grammar -> xprod list

  module Tree :
   sig
    type tree =
    | Leaf of Ty.terminal
    | Node of Ty.nonterminal * tree list

    val tree_rect :
      (Ty.terminal -> 'a1) -> (Ty.nonterminal -> tree list -> 'a1) -> tree -> 'a1

    val tree_rec :
      (Ty.terminal -> 'a1) -> (Ty.nonterminal -> tree list -> 'a1) -> tree -> 'a1

    val isNode : tree -> bool

    val isLeaf : tree -> bool
   end

  module Lookahead :
   sig
    type lookahead =
    | LA of Ty.terminal
    | EOF

    val lookahead_rect : (Ty.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

    val lookahead_rec : (Ty.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

    val show_lookahead : lookahead -> char list
   end

  module Collections :
   sig
    module MDT_NT :
     sig
      type t = Ty.nonterminal

      val eq_dec : Ty.nonterminal -> Ty.nonterminal -> bool
     end

    module NT_as_DT :
     sig
      type t = Ty.nonterminal

      val eq_dec : Ty.nonterminal -> Ty.nonterminal -> bool
     end

    module NtSet :
     sig
      module Raw :
       sig
        type elt = Ty.nonterminal

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
        type t = Ty.nonterminal

        val eq_dec : Ty.nonterminal -> Ty.nonterminal -> bool
       end

      type elt = Ty.nonterminal

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

    module NtMap :
     sig
      module Raw :
       sig
        module PX :
         sig
         end

        type key = Ty.nonterminal

        type 'elt t = (Ty.nonterminal * 'elt) list

        val empty : 'a1 t

        val is_empty : 'a1 t -> bool

        val mem : key -> 'a1 t -> bool

        type 'elt coq_R_mem =
        | R_mem_0 of 'elt t
        | R_mem_1 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
        | R_mem_2 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
           * bool * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
          'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem ->
          'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
        | R_find_2 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
           * 'elt option * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
          coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1
          coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
        | R_add_2 of 'elt t * Ty.nonterminal * 'elt * (Ty.nonterminal * 'elt) list
           * 'elt t * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
          -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add
          -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * Ty.nonterminal * 'elt
           * (Ty.nonterminal * 'elt) list
        | R_remove_2 of 'elt t * Ty.nonterminal * 'elt
           * (Ty.nonterminal * 'elt) list * 'elt t * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
          coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1
          coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> Ty.nonterminal -> 'a1 ->
          (Ty.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
          Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> __ -> __ ->
          'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * Ty.nonterminal * 'elt
           * (Ty.nonterminal * 'elt) list * 'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> 'a2
          -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
          'a2) coq_R_fold -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> 'a2
          -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1,
          'a2) coq_R_fold -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> 'a3
          -> 'a3) -> 'a1 t -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> Ty.nonterminal -> 'a1 -> (Ty.nonterminal * 'a1) list -> __ -> 'a3
          -> 'a3) -> 'a1 t -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

        val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

        val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val at_least_left :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_right :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
          list

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
          'a3 option
       end

      module E :
       sig
        type t = Ty.nonterminal

        val eq_dec : Ty.nonterminal -> Ty.nonterminal -> bool
       end

      type key = Ty.nonterminal

      type 'elt slist =
        'elt Raw.t
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

    val lookahead_eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool

    module MDT_Lookahead :
     sig
      type t = Lookahead.lookahead

      val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
     end

    module Lookahead_as_DT :
     sig
      type t = Lookahead.lookahead

      val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
     end

    module LaSet :
     sig
      module Raw :
       sig
        type elt = Lookahead.lookahead

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
        type t = Lookahead.lookahead

        val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      type elt = Lookahead.lookahead

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

    type pt_key = Ty.nonterminal * Lookahead.lookahead

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
        | R_mem_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * bool
           * 'elt coq_R_mem

        val coq_R_mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val coq_R_mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem -> 'a2 ->
          'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

        val mem_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val mem_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

        val find : key -> 'a1 t -> 'a1 option

        type 'elt coq_R_find =
        | R_find_0 of 'elt t
        | R_find_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
        | R_find_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt option
           * 'elt coq_R_find

        val coq_R_find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val coq_R_find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1 coq_R_find ->
          'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

        val find_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val find_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

        val add : key -> 'a1 -> 'a1 t -> 'a1 t

        type 'elt coq_R_add =
        | R_add_0 of 'elt t
        | R_add_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
        | R_add_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
           * 'elt coq_R_add

        val coq_R_add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1
          -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val coq_R_add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1
          -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

        val add_rect :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1
          -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val add_rec :
          key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1
          -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

        val remove : key -> 'a1 t -> 'a1 t

        type 'elt coq_R_remove =
        | R_remove_0 of 'elt t
        | R_remove_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
        | R_remove_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
           * 'elt coq_R_remove

        val coq_R_remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val coq_R_remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2
          -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

        val remove_rect :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val remove_rec :
          key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 -> (pt_key * 'a1)
          list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
          (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

        val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

        val elements : 'a1 t -> 'a1 t

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        type ('elt, 'a) coq_R_fold =
        | R_fold_0 of 'elt t * 'a
        | R_fold_1 of 'elt t * 'a * pt_key * 'elt * (pt_key * 'elt) list * 
           'a * ('elt, 'a) coq_R_fold

        val coq_R_fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
          -> 'a3

        val coq_R_fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
          coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold
          -> 'a3

        val fold_rect :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
          -> 'a2 -> 'a3

        val fold_rec :
          (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
          'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
          -> 'a2 -> 'a3

        val coq_R_fold_correct :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold

        val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

        val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

        val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

        val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

        val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val fold_right_pair :
          ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

        val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

        val at_least_left :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_right :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val at_least_one :
          'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

        val option_cons : key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key * 'a3)
          list

        val at_least_one_then_f :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
          'a3 option
       end

      module E :
       sig
        type t = pt_key

        val eq_dec : pt_key -> pt_key -> bool
       end

      type key = pt_key

      type 'elt slist =
        'elt Raw.t
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

    type first_map = LaSet.t NtMap.t

    type follow_map = LaSet.t NtMap.t

    type parse_table = xprod ParseTable.t
   end

  module CollectionFacts :
   sig
    module NtSetFacts :
     sig
      val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
     end

    module NtSetEqProps :
     sig
      module MP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
         end

        val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

        val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

        val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

        val fold_rec :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          'a2 -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.NtSet.t -> 'a2

        val fold_rel :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 ->
          (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
          -> Collections.NtSet.t -> 'a1

        val set_induction_bis :
          (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.NtSet.t -> 'a1

        val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

        val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
       end

      val choose_mem_3 : Collections.NtSet.t -> Collections.NtSet.elt

      val set_rec :
        (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
        (Collections.NtSet.t -> Collections.NtSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
        -> Collections.NtSet.t -> 'a1

      val for_all_mem_4 :
        (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
        Collections.NtSet.elt

      val exists_mem_4 :
        (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
        Collections.NtSet.elt

      val sum : (Collections.NtSet.elt -> nat) -> Collections.NtSet.t -> nat
     end

    module NtMapFacts :
     sig
      val eqb : Ty.nonterminal -> Ty.nonterminal -> bool

      val coq_In_dec : 'a1 Collections.NtMap.t -> Collections.NtMap.key -> bool
     end

    module LaSetFacts :
     sig
      val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
     end

    module LaSetEqProps :
     sig
      module MP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

        val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

        val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

        val fold_rec :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          'a2 -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.LaSet.t -> 'a2

        val fold_rel :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 ->
          (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
          -> Collections.LaSet.t -> 'a1

        val set_induction_bis :
          (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.LaSet.t -> 'a1

        val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

        val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
       end

      val choose_mem_3 : Collections.LaSet.t -> Collections.LaSet.elt

      val set_rec :
        (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
        (Collections.LaSet.t -> Collections.LaSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
        -> Collections.LaSet.t -> 'a1

      val for_all_mem_4 :
        (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
        Collections.LaSet.elt

      val exists_mem_4 :
        (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
        Collections.LaSet.elt

      val sum : (Collections.LaSet.elt -> nat) -> Collections.LaSet.t -> nat
     end

    module ParseTableFacts :
     sig
      val eqb : Collections.pt_key -> Collections.pt_key -> bool

      val coq_In_dec :
        'a1 Collections.ParseTable.t -> Collections.ParseTable.key -> bool
     end

    module NP :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
       end

      val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

      val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

      val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

      val fold_rec :
        (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
        (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
        Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 -> 'a2)
        -> 'a2

      val fold_rec_bis :
        (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
        (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
        'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> __ ->
        'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t -> 'a2
        -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
        Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
        (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 -> 'a2)
        -> Collections.NtSet.t -> 'a2

      val fold_rel :
        (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2 ->
        'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 -> (Collections.NtSet.elt
        -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
        Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1) ->
        Collections.NtSet.t -> 'a1

      val set_induction_bis :
        (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
        (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
        Collections.NtSet.t -> 'a1

      val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

      val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
     end

    module ND :
     sig
      module F :
       sig
        val eqb : Ty.nonterminal -> Ty.nonterminal -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module LP :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

      val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

      val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

      val fold_rec :
        (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
        (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
        Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 -> 'a2)
        -> 'a2

      val fold_rec_bis :
        (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
        (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
        'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> __ ->
        'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t -> 'a2
        -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
        Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
        (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 -> 'a2)
        -> Collections.LaSet.t -> 'a2

      val fold_rel :
        (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2 ->
        'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 -> (Collections.LaSet.elt
        -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
        Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1) ->
        Collections.LaSet.t -> 'a1

      val set_induction_bis :
        (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
        (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
        Collections.LaSet.t -> 'a1

      val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

      val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
     end

    module LD :
     sig
      module F :
       sig
        val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end
   end

  module Derivation :
   sig
    val peek : token list -> Lookahead.lookahead
   end

  module Utils :
   sig
    val isNT : symbol -> bool

    val isT : symbol -> bool

    val lhs : xprod -> Ty.nonterminal

    val rhs : xprod -> symbol list

    val prodOf : xprod -> production

    val prodsOf : grammar -> production list

    val pt_lookup :
      Ty.nonterminal -> Lookahead.lookahead -> Collections.parse_table -> xprod
      option

    val pt_add :
      Ty.nonterminal -> Lookahead.lookahead -> xprod -> Collections.parse_table ->
      Collections.parse_table

    val fromNtList : Ty.nonterminal list -> Collections.NtSet.t
   end

  module Specs :
   sig
    type first_map = Collections.LaSet.t Collections.NtMap.t

    type follow_map = Collections.LaSet.t Collections.NtMap.t
   end
 end

module type T =
 sig
  module SymTy :
   SYMBOL_TYPES

  module Defs :
   sig
    type symbol =
    | T of SymTy.terminal
    | NT of SymTy.nonterminal

    val symbol_rect :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1) -> symbol -> 'a1

    type production = SymTy.nonterminal * symbol list

    val symbol_eq_dec : symbol -> symbol -> bool

    val show_symbol : symbol -> char list

    val prependToAll : char list -> char list list -> char list

    val intersperse : char list -> char list list -> char list

    val show_rhs : symbol list -> char list

    val show_prod : production -> char list

    type symbol_semty = __

    type tuple = __

    type rhs_semty = tuple

    type action_ty = __

    type xprod = (production, action_ty) sigT

    type token = (SymTy.terminal, SymTy.t_semty) sigT

    type grammar = { start : SymTy.nonterminal; prods : xprod list }

    val start : grammar -> SymTy.nonterminal

    val prods : grammar -> xprod list

    module Tree :
     sig
      type tree =
      | Leaf of SymTy.terminal
      | Node of SymTy.nonterminal * tree list

      val tree_rect :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree list -> 'a1) -> tree
        -> 'a1

      val tree_rec :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree list -> 'a1) -> tree
        -> 'a1

      val isNode : tree -> bool

      val isLeaf : tree -> bool
     end

    module Lookahead :
     sig
      type lookahead =
      | LA of SymTy.terminal
      | EOF

      val lookahead_rect : (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

      val lookahead_rec : (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

      val show_lookahead : lookahead -> char list
     end

    module Collections :
     sig
      module MDT_NT :
       sig
        type t = SymTy.nonterminal

        val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NT_as_DT :
       sig
        type t = SymTy.nonterminal

        val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NtSet :
       sig
        module Raw :
         sig
          type elt = SymTy.nonterminal

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
          type t = SymTy.nonterminal

          val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        type elt = SymTy.nonterminal

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

      module NtMap :
       sig
        module Raw :
         sig
          module PX :
           sig
           end

          type key = SymTy.nonterminal

          type 'elt t = (SymTy.nonterminal * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_mem_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_find_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_add_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt t * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_remove_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt t * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

          val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
            'a3 option
         end

        module E :
         sig
          type t = SymTy.nonterminal

          val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        type key = SymTy.nonterminal

        type 'elt slist =
          'elt Raw.t
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

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val lookahead_eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool

      module MDT_Lookahead :
       sig
        type t = Lookahead.lookahead

        val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module Lookahead_as_DT :
       sig
        type t = Lookahead.lookahead

        val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module LaSet :
       sig
        module Raw :
         sig
          type elt = Lookahead.lookahead

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
          type t = Lookahead.lookahead

          val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        type elt = Lookahead.lookahead

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

      type pt_key = SymTy.nonterminal * Lookahead.lookahead

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
          | R_mem_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
            -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
            -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_find_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
            'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
            'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_add_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
            -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
            -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_remove_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * pt_key * 'elt * (pt_key * 'elt) list * 
             'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
            t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
            t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

          val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
            'a3 option
         end

        module E :
         sig
          type t = pt_key

          val eq_dec : pt_key -> pt_key -> bool
         end

        type key = pt_key

        type 'elt slist =
          'elt Raw.t
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

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      type first_map = LaSet.t NtMap.t

      type follow_map = LaSet.t NtMap.t

      type parse_table = xprod ParseTable.t
     end

    module CollectionFacts :
     sig
      module NtSetFacts :
       sig
        val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NtSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
           end

          val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

          val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

          val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

          val fold_rec :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
            Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            'a2 -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
            Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 ->
            'a2) -> Collections.NtSet.t -> 'a2

          val fold_rel :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2
            -> 'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 ->
            (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
            Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
            -> Collections.NtSet.t -> 'a1

          val set_induction_bis :
            (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1
            -> (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1)
            -> Collections.NtSet.t -> 'a1

          val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

          val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
         end

        val choose_mem_3 : Collections.NtSet.t -> Collections.NtSet.elt

        val set_rec :
          (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          (Collections.NtSet.t -> Collections.NtSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.NtSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
          Collections.NtSet.elt

        val exists_mem_4 :
          (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
          Collections.NtSet.elt

        val sum : (Collections.NtSet.elt -> nat) -> Collections.NtSet.t -> nat
       end

      module NtMapFacts :
       sig
        val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool

        val coq_In_dec : 'a1 Collections.NtMap.t -> Collections.NtMap.key -> bool
       end

      module LaSetFacts :
       sig
        val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module LaSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
           end

          val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

          val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

          val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

          val fold_rec :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
            Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            'a2 -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
            Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 ->
            'a2) -> Collections.LaSet.t -> 'a2

          val fold_rel :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2
            -> 'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 ->
            (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
            Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
            -> Collections.LaSet.t -> 'a1

          val set_induction_bis :
            (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1
            -> (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1)
            -> Collections.LaSet.t -> 'a1

          val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

          val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
         end

        val choose_mem_3 : Collections.LaSet.t -> Collections.LaSet.elt

        val set_rec :
          (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          (Collections.LaSet.t -> Collections.LaSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.LaSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
          Collections.LaSet.elt

        val exists_mem_4 :
          (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
          Collections.LaSet.elt

        val sum : (Collections.LaSet.elt -> nat) -> Collections.LaSet.t -> nat
       end

      module ParseTableFacts :
       sig
        val eqb : Collections.pt_key -> Collections.pt_key -> bool

        val coq_In_dec :
          'a1 Collections.ParseTable.t -> Collections.ParseTable.key -> bool
       end

      module NP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

        val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

        val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

        val fold_rec :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          'a2 -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.NtSet.t -> 'a2

        val fold_rel :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 ->
          (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
          -> Collections.NtSet.t -> 'a1

        val set_induction_bis :
          (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.NtSet.t -> 'a1

        val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

        val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
       end

      module ND :
       sig
        module F :
         sig
          val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module LP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

        val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

        val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

        val fold_rec :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          'a2 -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.LaSet.t -> 'a2

        val fold_rel :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 ->
          (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
          -> Collections.LaSet.t -> 'a1

        val set_induction_bis :
          (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.LaSet.t -> 'a1

        val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

        val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
       end

      module LD :
       sig
        module F :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end
     end

    module Derivation :
     sig
      val peek : token list -> Lookahead.lookahead
     end

    module Utils :
     sig
      val isNT : symbol -> bool

      val isT : symbol -> bool

      val lhs : xprod -> SymTy.nonterminal

      val rhs : xprod -> symbol list

      val prodOf : xprod -> production

      val prodsOf : grammar -> production list

      val pt_lookup :
        SymTy.nonterminal -> Lookahead.lookahead -> Collections.parse_table ->
        xprod option

      val pt_add :
        SymTy.nonterminal -> Lookahead.lookahead -> xprod ->
        Collections.parse_table -> Collections.parse_table

      val fromNtList : SymTy.nonterminal list -> Collections.NtSet.t
     end

    module Specs :
     sig
      type first_map = Collections.LaSet.t Collections.NtMap.t

      type follow_map = Collections.LaSet.t Collections.NtMap.t
     end
   end
 end

module LemmasFn :
 functor (G:T) ->
 sig
  val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
 end

module ParserFn :
 functor (G:T) ->
 sig
  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end

  val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

  val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

  type sym_arg =
  | F_arg of G.Defs.symbol
  | G_arg of G.Defs.symbol list

  val sym_arg_rect :
    (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

  val sym_arg_rec :
    (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

  val sa_size : sym_arg -> nat

  val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

  val ptlk_dec :
    G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
    G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

  val meas :
    G.Defs.Collections.parse_table -> G.Defs.token list ->
    G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

  type parse_failure =
  | Reject of char list * G.Defs.token list
  | Error of char list * G.SymTy.nonterminal * G.Defs.token list

  val parse_failure_rect :
    (char list -> G.Defs.token list -> 'a1) -> (char list -> G.SymTy.nonterminal ->
    G.Defs.token list -> 'a1) -> parse_failure -> 'a1

  val parse_failure_rec :
    (char list -> G.Defs.token list -> 'a1) -> (char list -> G.SymTy.nonterminal ->
    G.Defs.token list -> 'a1) -> parse_failure -> 'a1

  val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

  type 'a length_lt_eq = bool

  val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

  val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

  val length_lt_eq_trans :
    'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1 length_lt_eq -> 'a1
    length_lt_eq

  val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

  val parseTree :
    G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
    G.Defs.Collections.NtSet.t -> (parse_failure,
    G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT) sum

  val parseForest :
    G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token list ->
    G.Defs.Collections.NtSet.t -> (parse_failure, G.Defs.rhs_semty * (G.Defs.token
    list, G.Defs.token length_lt_eq) sigT) sum
 end

val findDup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 option

module GeneratorFn :
 functor (G:T) ->
 sig
  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end

  val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

  val nullableGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

  val updateNu :
    G.Defs.production -> G.Defs.Collections.NtSet.t -> G.Defs.Collections.NtSet.t

  val nullablePass :
    G.Defs.production list -> G.Defs.Collections.NtSet.t ->
    G.Defs.Collections.NtSet.t

  val countNullableCandidates :
    G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

  val mkNullableSet'_func :
    (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
    G.Defs.Collections.NtSet.t

  val mkNullableSet' :
    G.Defs.production list -> G.Defs.Collections.NtSet.t ->
    G.Defs.Collections.NtSet.t

  val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

  val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

  val findOrEmpty :
    G.SymTy.nonterminal -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

  val firstSym :
    G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

  val firstGamma :
    G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
    G.Defs.Collections.LaSet.t

  val updateFi :
    G.Defs.Collections.NtSet.t -> G.Defs.production -> G.Defs.Specs.first_map ->
    G.Defs.Specs.first_map

  val firstPass :
    G.Defs.production list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
    -> G.Defs.Specs.first_map

  val first_map_equiv_dec : G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

  type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

  val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

  module MDT_Pair :
   sig
    type t = nt_la_pair

    val eq_dec : nt_la_pair -> nt_la_pair -> bool
   end

  module Pair_as_DT :
   sig
    type t = nt_la_pair

    val eq_dec : nt_la_pair -> nt_la_pair -> bool
   end

  module PairSet :
   sig
    module Raw :
     sig
      type elt = nt_la_pair

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
      type t = nt_la_pair

      val eq_dec : nt_la_pair -> nt_la_pair -> bool
     end

    type elt = nt_la_pair

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

  module PairSetFacts :
   sig
    val eqb : nt_la_pair -> nt_la_pair -> bool
   end

  module PairSetEqProps :
   sig
    module MP :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : nt_la_pair -> nt_la_pair -> bool
       end

      val coq_In_dec : PairSet.elt -> PairSet.t -> bool

      val of_list : PairSet.elt list -> PairSet.t

      val to_list : PairSet.t -> PairSet.elt list

      val fold_rec :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ -> 'a2)
        -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __ -> 'a2
        -> 'a2) -> 'a2

      val fold_rec_bis :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> PairSet.t
        -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t ->
        __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ -> 'a2 ->
        'a2) -> PairSet.t -> 'a2

      val fold_rel :
        (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 -> PairSet.elt
        -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

      val set_induction_bis :
        (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
        PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

      val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

      val cardinal_inv_2b : PairSet.t -> PairSet.elt
     end

    val choose_mem_3 : PairSet.t -> PairSet.elt

    val set_rec :
      (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t -> PairSet.elt ->
      __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

    val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

    val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

    val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
   end

  module PP :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : nt_la_pair -> nt_la_pair -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    module FM :
     sig
      val eqb : nt_la_pair -> nt_la_pair -> bool
     end

    val coq_In_dec : PairSet.elt -> PairSet.t -> bool

    val of_list : PairSet.elt list -> PairSet.t

    val to_list : PairSet.t -> PairSet.elt list

    val fold_rec :
      (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ -> 'a2)
      -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_bis :
      (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> PairSet.t ->
      'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ ->
      __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt -> 'a1
      -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ -> 'a2 -> 'a2)
      -> PairSet.t -> 'a2

    val fold_rel :
      (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
      PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 -> PairSet.elt ->
      __ -> __ -> 'a1) -> PairSet.t -> 'a1

    val set_induction_bis :
      (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
      PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

    val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

    val cardinal_inv_2b : PairSet.t -> PairSet.elt
   end

  module PD :
   sig
    module F :
     sig
      val eqb : nt_la_pair -> nt_la_pair -> bool
     end

    module MSetLogicalFacts :
     sig
     end

    module MSetDecideAuxiliary :
     sig
     end

    module MSetDecideTestCases :
     sig
     end
   end

  val mkPairs : G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

  val pairsOf : G.Defs.Specs.first_map -> PairSet.t

  val leftmostLookahead : G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

  val leftmostLookaheads' : G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

  val leftmostLookaheads : G.Defs.production list -> G.Defs.Collections.LaSet.t

  val product :
    G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

  val numFirstCandidates : G.Defs.production list -> G.Defs.Specs.first_map -> nat

  val mkFirstMap'_func :
    (G.Defs.production list, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map,
    __) sigT) sigT) sigT -> G.Defs.Specs.first_map

  val mkFirstMap' :
    G.Defs.production list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
    -> G.Defs.Specs.first_map

  val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

  val mkFirstMap :
    G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

  val updateFo' :
    G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.SymTy.nonterminal ->
    G.Defs.symbol list -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

  val updateFo :
    G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.production ->
    G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

  val followPass :
    G.Defs.production list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
    -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

  val follow_map_equiv_dec :
    G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

  val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

  val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

  val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

  val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

  val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

  val numFollowCandidates : G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

  val mkFollowMap'_func :
    (G.Defs.grammar, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map, (__,
    (G.Defs.Specs.follow_map, __) sigT) sigT) sigT) sigT) sigT ->
    G.Defs.Specs.follow_map

  val mkFollowMap' :
    G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
    G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

  val initial_fo :
    G.Defs.grammar -> G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

  val mkFollowMap :
    G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
    G.Defs.Specs.follow_map

  type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

  val fromLookaheadList :
    G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

  val firstGamma' :
    G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
    G.Defs.Lookahead.lookahead list

  val firstEntries :
    G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
    table_entry list

  val followLookahead :
    G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
    G.Defs.Specs.follow_map -> G.Defs.Lookahead.lookahead list

  val followEntries :
    G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
    table_entry list

  val entriesForProd :
    G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.Specs.follow_map
    -> G.Defs.xprod -> table_entry list

  val mkEntries' :
    G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.Specs.follow_map
    -> G.Defs.xprod list -> table_entry list

  val mkEntries :
    G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.Specs.follow_map
    -> G.Defs.grammar -> table_entry list

  val ambigMessage :
    G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol list ->
    G.Defs.symbol list -> char list

  val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

  val addEntry :
    table_entry -> (char list, G.Defs.Collections.parse_table) sum -> (char list,
    G.Defs.Collections.parse_table) sum

  val mkParseTable :
    table_entry list -> (char list, G.Defs.Collections.parse_table) sum

  val dupMessage : G.Defs.production -> char list
 end

module NullableProofsFn :
 functor (G:T) ->
 sig
  module Gen :
   sig
    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end

    val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

    val nullableGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

    val updateNu :
      G.Defs.production -> G.Defs.Collections.NtSet.t -> G.Defs.Collections.NtSet.t

    val nullablePass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.NtSet.t

    val countNullableCandidates :
      G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

    val mkNullableSet'_func :
      (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
      G.Defs.Collections.NtSet.t

    val mkNullableSet' :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.NtSet.t

    val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

    val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

    val findOrEmpty :
      G.SymTy.nonterminal -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

    val firstSym :
      G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

    val firstGamma :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t

    val updateFi :
      G.Defs.Collections.NtSet.t -> G.Defs.production -> G.Defs.Specs.first_map ->
      G.Defs.Specs.first_map

    val firstPass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map

    val first_map_equiv_dec :
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

    type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

    val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

    module MDT_Pair :
     sig
      type t = nt_la_pair

      val eq_dec : nt_la_pair -> nt_la_pair -> bool
     end

    module Pair_as_DT :
     sig
      type t = nt_la_pair

      val eq_dec : nt_la_pair -> nt_la_pair -> bool
     end

    module PairSet :
     sig
      module Raw :
       sig
        type elt = nt_la_pair

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
        type t = nt_la_pair

        val eq_dec : nt_la_pair -> nt_la_pair -> bool
       end

      type elt = nt_la_pair

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

    module PairSetFacts :
     sig
      val eqb : nt_la_pair -> nt_la_pair -> bool
     end

    module PairSetEqProps :
     sig
      module MP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        val coq_In_dec : PairSet.elt -> PairSet.t -> bool

        val of_list : PairSet.elt list -> PairSet.t

        val to_list : PairSet.t -> PairSet.elt list

        val fold_rec :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ ->
          'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
          PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
          PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt ->
          'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ -> 'a2
          -> 'a2) -> PairSet.t -> 'a2

        val fold_rel :
          (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
          -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3

        val set_induction :
          (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 -> PairSet.elt
          -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

        val set_induction_bis :
          (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
          PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

        val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

        val cardinal_inv_2b : PairSet.t -> PairSet.elt
       end

      val choose_mem_3 : PairSet.t -> PairSet.elt

      val set_rec :
        (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t -> PairSet.elt
        -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

      val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

      val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

      val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
     end

    module PP :
     sig
      module Dec :
       sig
        module F :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module FM :
       sig
        val eqb : nt_la_pair -> nt_la_pair -> bool
       end

      val coq_In_dec : PairSet.elt -> PairSet.t -> bool

      val of_list : PairSet.elt list -> PairSet.t

      val to_list : PairSet.t -> PairSet.elt list

      val fold_rec :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ -> 'a2)
        -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __ -> 'a2
        -> 'a2) -> 'a2

      val fold_rec_bis :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> PairSet.t
        -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t ->
        __ -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_nodep :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt ->
        'a1 -> __ -> 'a2 -> 'a2) -> 'a2

      val fold_rec_weak :
        (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 -> __
        -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ -> 'a2 ->
        'a2) -> PairSet.t -> 'a2

      val fold_rel :
        (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
        PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

      val set_induction :
        (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 -> PairSet.elt
        -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

      val set_induction_bis :
        (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
        PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

      val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

      val cardinal_inv_2b : PairSet.t -> PairSet.elt
     end

    module PD :
     sig
      module F :
       sig
        val eqb : nt_la_pair -> nt_la_pair -> bool
       end

      module MSetLogicalFacts :
       sig
       end

      module MSetDecideAuxiliary :
       sig
       end

      module MSetDecideTestCases :
       sig
       end
     end

    val mkPairs : G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

    val pairsOf : G.Defs.Specs.first_map -> PairSet.t

    val leftmostLookahead : G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

    val leftmostLookaheads' : G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

    val leftmostLookaheads : G.Defs.production list -> G.Defs.Collections.LaSet.t

    val product :
      G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

    val numFirstCandidates : G.Defs.production list -> G.Defs.Specs.first_map -> nat

    val mkFirstMap'_func :
      (G.Defs.production list, (G.Defs.Collections.NtSet.t,
      (G.Defs.Specs.first_map, __) sigT) sigT) sigT -> G.Defs.Specs.first_map

    val mkFirstMap' :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map

    val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

    val mkFirstMap :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

    val updateFo' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.SymTy.nonterminal
      -> G.Defs.symbol list -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

    val updateFo :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.production ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

    val followPass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

    val follow_map_equiv_dec :
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

    val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

    val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

    val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

    val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

    val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

    val numFollowCandidates : G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

    val mkFollowMap'_func :
      (G.Defs.grammar, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map, (__,
      (G.Defs.Specs.follow_map, __) sigT) sigT) sigT) sigT) sigT ->
      G.Defs.Specs.follow_map

    val mkFollowMap' :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

    val initial_fo :
      G.Defs.grammar -> G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

    val mkFollowMap :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map

    type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

    val fromLookaheadList :
      G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

    val firstGamma' :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Lookahead.lookahead list

    val firstEntries :
      G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      table_entry list

    val followLookahead :
      G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.follow_map -> G.Defs.Lookahead.lookahead list

    val followEntries :
      G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
      table_entry list

    val entriesForProd :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

    val mkEntries' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

    val mkEntries :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

    val ambigMessage :
      G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol list ->
      G.Defs.symbol list -> char list

    val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

    val addEntry :
      table_entry -> (char list, G.Defs.Collections.parse_table) sum -> (char list,
      G.Defs.Collections.parse_table) sum

    val mkParseTable :
      table_entry list -> (char list, G.Defs.Collections.parse_table) sum

    val dupMessage : G.Defs.production -> char list
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module FirstProofsFn :
 functor (G:T) ->
 sig
  module NullableProofs :
   sig
    module Gen :
     sig
      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end

      val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

      val nullableGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

      val updateNu :
        G.Defs.production -> G.Defs.Collections.NtSet.t ->
        G.Defs.Collections.NtSet.t

      val nullablePass :
        G.Defs.production list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Collections.NtSet.t

      val countNullableCandidates :
        G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

      val mkNullableSet'_func :
        (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
        G.Defs.Collections.NtSet.t

      val mkNullableSet' :
        G.Defs.production list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Collections.NtSet.t

      val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

      val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

      val findOrEmpty :
        G.SymTy.nonterminal -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

      val firstSym :
        G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

      val firstGamma :
        G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
        -> G.Defs.Collections.LaSet.t

      val updateFi :
        G.Defs.Collections.NtSet.t -> G.Defs.production -> G.Defs.Specs.first_map
        -> G.Defs.Specs.first_map

      val firstPass :
        G.Defs.production list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Specs.first_map -> G.Defs.Specs.first_map

      val first_map_equiv_dec :
        G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

      type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

      val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

      module MDT_Pair :
       sig
        type t = nt_la_pair

        val eq_dec : nt_la_pair -> nt_la_pair -> bool
       end

      module Pair_as_DT :
       sig
        type t = nt_la_pair

        val eq_dec : nt_la_pair -> nt_la_pair -> bool
       end

      module PairSet :
       sig
        module Raw :
         sig
          type elt = nt_la_pair

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
          type t = nt_la_pair

          val eq_dec : nt_la_pair -> nt_la_pair -> bool
         end

        type elt = nt_la_pair

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

      module PairSetFacts :
       sig
        val eqb : nt_la_pair -> nt_la_pair -> bool
       end

      module PairSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          val coq_In_dec : PairSet.elt -> PairSet.t -> bool

          val of_list : PairSet.elt list -> PairSet.t

          val to_list : PairSet.t -> PairSet.elt list

          val fold_rec :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ ->
            'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a2

          val fold_rec_bis :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
            PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
            PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt
            -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ ->
            'a2 -> 'a2) -> PairSet.t -> 'a2

          val fold_rel :
            (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 ->
            'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
            'a3) -> 'a3

          val set_induction :
            (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
            PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

          val set_induction_bis :
            (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
            PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

          val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

          val cardinal_inv_2b : PairSet.t -> PairSet.elt
         end

        val choose_mem_3 : PairSet.t -> PairSet.elt

        val set_rec :
          (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t -> PairSet.elt
          -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

        val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

        val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

        val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
       end

      module PP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        val coq_In_dec : PairSet.elt -> PairSet.t -> bool

        val of_list : PairSet.elt list -> PairSet.t

        val to_list : PairSet.t -> PairSet.elt list

        val fold_rec :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ ->
          'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __
          -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
          PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
          PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt ->
          'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 ->
          __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ -> 'a2
          -> 'a2) -> PairSet.t -> 'a2

        val fold_rel :
          (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
          -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) ->
          'a3

        val set_induction :
          (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 -> PairSet.elt
          -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

        val set_induction_bis :
          (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
          PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

        val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

        val cardinal_inv_2b : PairSet.t -> PairSet.elt
       end

      module PD :
       sig
        module F :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      val mkPairs : G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

      val pairsOf : G.Defs.Specs.first_map -> PairSet.t

      val leftmostLookahead :
        G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

      val leftmostLookaheads' :
        G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

      val leftmostLookaheads : G.Defs.production list -> G.Defs.Collections.LaSet.t

      val product :
        G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

      val numFirstCandidates :
        G.Defs.production list -> G.Defs.Specs.first_map -> nat

      val mkFirstMap'_func :
        (G.Defs.production list, (G.Defs.Collections.NtSet.t,
        (G.Defs.Specs.first_map, __) sigT) sigT) sigT -> G.Defs.Specs.first_map

      val mkFirstMap' :
        G.Defs.production list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Specs.first_map -> G.Defs.Specs.first_map

      val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

      val mkFirstMap :
        G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

      val updateFo' :
        G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.SymTy.nonterminal
        -> G.Defs.symbol list -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

      val updateFo :
        G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.production
        -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

      val followPass :
        G.Defs.production list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Specs.first_map -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

      val follow_map_equiv_dec :
        G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

      val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

      val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

      val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

      val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

      val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

      val numFollowCandidates : G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

      val mkFollowMap'_func :
        (G.Defs.grammar, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map, (__,
        (G.Defs.Specs.follow_map, __) sigT) sigT) sigT) sigT) sigT ->
        G.Defs.Specs.follow_map

      val mkFollowMap' :
        G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

      val initial_fo :
        G.Defs.grammar -> G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

      val mkFollowMap :
        G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        G.Defs.Specs.follow_map

      type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

      val fromLookaheadList :
        G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

      val firstGamma' :
        G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
        -> G.Defs.Lookahead.lookahead list

      val firstEntries :
        G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        table_entry list

      val followLookahead :
        G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
        G.Defs.Specs.follow_map -> G.Defs.Lookahead.lookahead list

      val followEntries :
        G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
        table_entry list

      val entriesForProd :
        G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

      val mkEntries' :
        G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

      val mkEntries :
        G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
        G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

      val ambigMessage :
        G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol list ->
        G.Defs.symbol list -> char list

      val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

      val addEntry :
        table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
        (char list, G.Defs.Collections.parse_table) sum

      val mkParseTable :
        table_entry list -> (char list, G.Defs.Collections.parse_table) sum

      val dupMessage : G.Defs.production -> char list
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module FollowProofsFn :
 functor (G:T) ->
 sig
  module FirstProofs :
   sig
    module NullableProofs :
     sig
      module Gen :
       sig
        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end

        val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

        val nullableGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

        val updateNu :
          G.Defs.production -> G.Defs.Collections.NtSet.t ->
          G.Defs.Collections.NtSet.t

        val nullablePass :
          G.Defs.production list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Collections.NtSet.t

        val countNullableCandidates :
          G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

        val mkNullableSet'_func :
          (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
          G.Defs.Collections.NtSet.t

        val mkNullableSet' :
          G.Defs.production list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Collections.NtSet.t

        val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

        val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

        val findOrEmpty :
          G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
          G.Defs.Collections.LaSet.t

        val firstSym :
          G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

        val firstGamma :
          G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

        val updateFi :
          G.Defs.Collections.NtSet.t -> G.Defs.production -> G.Defs.Specs.first_map
          -> G.Defs.Specs.first_map

        val firstPass :
          G.Defs.production list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Specs.first_map -> G.Defs.Specs.first_map

        val first_map_equiv_dec :
          G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

        type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

        val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

        module MDT_Pair :
         sig
          type t = nt_la_pair

          val eq_dec : nt_la_pair -> nt_la_pair -> bool
         end

        module Pair_as_DT :
         sig
          type t = nt_la_pair

          val eq_dec : nt_la_pair -> nt_la_pair -> bool
         end

        module PairSet :
         sig
          module Raw :
           sig
            type elt = nt_la_pair

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
            type t = nt_la_pair

            val eq_dec : nt_la_pair -> nt_la_pair -> bool
           end

          type elt = nt_la_pair

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

        module PairSetFacts :
         sig
          val eqb : nt_la_pair -> nt_la_pair -> bool
         end

        module PairSetEqProps :
         sig
          module MP :
           sig
            module Dec :
             sig
              module F :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              module MSetLogicalFacts :
               sig
               end

              module MSetDecideAuxiliary :
               sig
               end

              module MSetDecideTestCases :
               sig
               end
             end

            module FM :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            val coq_In_dec : PairSet.elt -> PairSet.t -> bool

            val of_list : PairSet.elt list -> PairSet.t

            val to_list : PairSet.t -> PairSet.elt list

            val fold_rec :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __
              -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_bis :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
              PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1
              -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_nodep :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
              (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_weak :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __
              -> 'a2 -> 'a2) -> PairSet.t -> 'a2

            val fold_rel :
              (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 ->
              'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
              'a3) -> 'a3

            val set_induction :
              (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
              PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

            val set_induction_bis :
              (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt
              -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

            val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

            val cardinal_inv_2b : PairSet.t -> PairSet.elt
           end

          val choose_mem_3 : PairSet.t -> PairSet.elt

          val set_rec :
            (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t ->
            PairSet.elt -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

          val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

          val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

          val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
         end

        module PP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          val coq_In_dec : PairSet.elt -> PairSet.t -> bool

          val of_list : PairSet.elt list -> PairSet.t

          val to_list : PairSet.t -> PairSet.elt list

          val fold_rec :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __ ->
            'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a2

          val fold_rec_bis :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
            PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
            PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 -> (PairSet.elt
            -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1 ->
            __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __ ->
            'a2 -> 'a2) -> PairSet.t -> 'a2

          val fold_rel :
            (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 ->
            'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
            'a3) -> 'a3

          val set_induction :
            (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
            PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

          val set_induction_bis :
            (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt ->
            PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

          val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

          val cardinal_inv_2b : PairSet.t -> PairSet.elt
         end

        module PD :
         sig
          module F :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        val mkPairs : G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

        val pairsOf : G.Defs.Specs.first_map -> PairSet.t

        val leftmostLookahead :
          G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

        val leftmostLookaheads' :
          G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

        val leftmostLookaheads :
          G.Defs.production list -> G.Defs.Collections.LaSet.t

        val product :
          G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

        val numFirstCandidates :
          G.Defs.production list -> G.Defs.Specs.first_map -> nat

        val mkFirstMap'_func :
          (G.Defs.production list, (G.Defs.Collections.NtSet.t,
          (G.Defs.Specs.first_map, __) sigT) sigT) sigT -> G.Defs.Specs.first_map

        val mkFirstMap' :
          G.Defs.production list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Specs.first_map -> G.Defs.Specs.first_map

        val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

        val mkFirstMap :
          G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

        val updateFo' :
          G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Specs.follow_map ->
          G.Defs.Specs.follow_map

        val updateFo :
          G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map -> G.Defs.production
          -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

        val followPass :
          G.Defs.production list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
          G.Defs.Specs.follow_map

        val follow_map_equiv_dec :
          G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

        val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

        val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

        val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

        val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

        val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

        val numFollowCandidates : G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

        val mkFollowMap'_func :
          (G.Defs.grammar, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map,
          (__, (G.Defs.Specs.follow_map, __) sigT) sigT) sigT) sigT) sigT ->
          G.Defs.Specs.follow_map

        val mkFollowMap' :
          G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

        val initial_fo :
          G.Defs.grammar -> G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

        val mkFollowMap :
          G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.Defs.Specs.follow_map

        type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

        val fromLookaheadList :
          G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

        val firstGamma' :
          G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
          G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead list

        val firstEntries :
          G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          table_entry list

        val followLookahead :
          G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Collections.NtSet.t
          -> G.Defs.Specs.follow_map -> G.Defs.Lookahead.lookahead list

        val followEntries :
          G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
          table_entry list

        val entriesForProd :
          G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

        val mkEntries' :
          G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

        val mkEntries :
          G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
          G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

        val ambigMessage :
          G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol list
          -> G.Defs.symbol list -> char list

        val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

        val addEntry :
          table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
          (char list, G.Defs.Collections.parse_table) sum

        val mkParseTable :
          table_entry list -> (char list, G.Defs.Collections.parse_table) sum

        val dupMessage : G.Defs.production -> char list
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module EntryProofsFn :
 functor (G:T) ->
 sig
  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end

  module FollowProofs :
   sig
    module FirstProofs :
     sig
      module NullableProofs :
       sig
        module Gen :
         sig
          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end

          val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

          val nullableGamma :
            G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

          val updateNu :
            G.Defs.production -> G.Defs.Collections.NtSet.t ->
            G.Defs.Collections.NtSet.t

          val nullablePass :
            G.Defs.production list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Collections.NtSet.t

          val countNullableCandidates :
            G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

          val mkNullableSet'_func :
            (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
            G.Defs.Collections.NtSet.t

          val mkNullableSet' :
            G.Defs.production list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Collections.NtSet.t

          val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

          val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

          val findOrEmpty :
            G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
            G.Defs.Collections.LaSet.t

          val firstSym :
            G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

          val firstGamma :
            G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

          val updateFi :
            G.Defs.Collections.NtSet.t -> G.Defs.production ->
            G.Defs.Specs.first_map -> G.Defs.Specs.first_map

          val firstPass :
            G.Defs.production list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Specs.first_map -> G.Defs.Specs.first_map

          val first_map_equiv_dec :
            G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

          type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

          val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

          module MDT_Pair :
           sig
            type t = nt_la_pair

            val eq_dec : nt_la_pair -> nt_la_pair -> bool
           end

          module Pair_as_DT :
           sig
            type t = nt_la_pair

            val eq_dec : nt_la_pair -> nt_la_pair -> bool
           end

          module PairSet :
           sig
            module Raw :
             sig
              type elt = nt_la_pair

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
              type t = nt_la_pair

              val eq_dec : nt_la_pair -> nt_la_pair -> bool
             end

            type elt = nt_la_pair

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

          module PairSetFacts :
           sig
            val eqb : nt_la_pair -> nt_la_pair -> bool
           end

          module PairSetEqProps :
           sig
            module MP :
             sig
              module Dec :
               sig
                module F :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                module MSetLogicalFacts :
                 sig
                 end

                module MSetDecideAuxiliary :
                 sig
                 end

                module MSetDecideTestCases :
                 sig
                 end
               end

              module FM :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              val coq_In_dec : PairSet.elt -> PairSet.t -> bool

              val of_list : PairSet.elt list -> PairSet.t

              val to_list : PairSet.t -> PairSet.elt list

              val fold_rec :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __
                -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ ->
                __ -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_bis :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1
                -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_nodep :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_weak :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t ->
                'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t
                -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

              val fold_rel :
                (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1
                -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ ->
                'a3 -> 'a3) -> 'a3

              val set_induction :
                (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

              val set_induction_bis :
                (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt
                -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

              val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

              val cardinal_inv_2b : PairSet.t -> PairSet.elt
             end

            val choose_mem_3 : PairSet.t -> PairSet.elt

            val set_rec :
              (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t ->
              PairSet.elt -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

            val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

            val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

            val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
           end

          module PP :
           sig
            module Dec :
             sig
              module F :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              module MSetLogicalFacts :
               sig
               end

              module MSetDecideAuxiliary :
               sig
               end

              module MSetDecideTestCases :
               sig
               end
             end

            module FM :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            val coq_In_dec : PairSet.elt -> PairSet.t -> bool

            val of_list : PairSet.elt list -> PairSet.t

            val to_list : PairSet.t -> PairSet.elt list

            val fold_rec :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __
              -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ -> __
              -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_bis :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
              PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1
              -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_nodep :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
              (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

            val fold_rec_weak :
              (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t -> 'a1
              -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t -> __
              -> 'a2 -> 'a2) -> PairSet.t -> 'a2

            val fold_rel :
              (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1 ->
              'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 ->
              'a3) -> 'a3

            val set_induction :
              (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
              PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

            val set_induction_bis :
              (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt
              -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

            val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

            val cardinal_inv_2b : PairSet.t -> PairSet.elt
           end

          module PD :
           sig
            module F :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          val mkPairs :
            G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

          val pairsOf : G.Defs.Specs.first_map -> PairSet.t

          val leftmostLookahead :
            G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

          val leftmostLookaheads' :
            G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

          val leftmostLookaheads :
            G.Defs.production list -> G.Defs.Collections.LaSet.t

          val product :
            G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

          val numFirstCandidates :
            G.Defs.production list -> G.Defs.Specs.first_map -> nat

          val mkFirstMap'_func :
            (G.Defs.production list, (G.Defs.Collections.NtSet.t,
            (G.Defs.Specs.first_map, __) sigT) sigT) sigT -> G.Defs.Specs.first_map

          val mkFirstMap' :
            G.Defs.production list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Specs.first_map -> G.Defs.Specs.first_map

          val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

          val mkFirstMap :
            G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

          val updateFo' :
            G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Specs.follow_map ->
            G.Defs.Specs.follow_map

          val updateFo :
            G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            G.Defs.production -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

          val followPass :
            G.Defs.production list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
            G.Defs.Specs.follow_map

          val follow_map_equiv_dec :
            G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

          val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

          val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

          val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

          val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

          val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

          val numFollowCandidates : G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

          val mkFollowMap'_func :
            (G.Defs.grammar, (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map,
            (__, (G.Defs.Specs.follow_map, __) sigT) sigT) sigT) sigT) sigT ->
            G.Defs.Specs.follow_map

          val mkFollowMap' :
            G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
            -> G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

          val initial_fo :
            G.Defs.grammar -> G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

          val mkFollowMap :
            G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
            -> G.Defs.Specs.follow_map

          type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

          val fromLookaheadList :
            G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

          val firstGamma' :
            G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
            G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead list

          val firstEntries :
            G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            table_entry list

          val followLookahead :
            G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Collections.NtSet.t
            -> G.Defs.Specs.follow_map -> G.Defs.Lookahead.lookahead list

          val followEntries :
            G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map
            -> table_entry list

          val entriesForProd :
            G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

          val mkEntries' :
            G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

          val mkEntries :
            G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
            G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

          val ambigMessage :
            G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol list
            -> G.Defs.symbol list -> char list

          val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

          val addEntry :
            table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
            (char list, G.Defs.Collections.parse_table) sum

          val mkParseTable :
            table_entry list -> (char list, G.Defs.Collections.parse_table) sum

          val dupMessage : G.Defs.production -> char list
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end
 end

module GeneratorProofsFn :
 functor (G:T) ->
 sig
  module EntryProofs :
   sig
    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end

    module FollowProofs :
     sig
      module FirstProofs :
       sig
        module NullableProofs :
         sig
          module Gen :
           sig
            module L :
             sig
              val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
             end

            val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

            val nullableGamma :
              G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

            val updateNu :
              G.Defs.production -> G.Defs.Collections.NtSet.t ->
              G.Defs.Collections.NtSet.t

            val nullablePass :
              G.Defs.production list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Collections.NtSet.t

            val countNullableCandidates :
              G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

            val mkNullableSet'_func :
              (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
              G.Defs.Collections.NtSet.t

            val mkNullableSet' :
              G.Defs.production list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Collections.NtSet.t

            val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

            val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

            val findOrEmpty :
              G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
              G.Defs.Collections.LaSet.t

            val firstSym :
              G.Defs.symbol -> G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

            val firstGamma :
              G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

            val updateFi :
              G.Defs.Collections.NtSet.t -> G.Defs.production ->
              G.Defs.Specs.first_map -> G.Defs.Specs.first_map

            val firstPass :
              G.Defs.production list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Specs.first_map

            val first_map_equiv_dec :
              G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

            type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

            val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

            module MDT_Pair :
             sig
              type t = nt_la_pair

              val eq_dec : nt_la_pair -> nt_la_pair -> bool
             end

            module Pair_as_DT :
             sig
              type t = nt_la_pair

              val eq_dec : nt_la_pair -> nt_la_pair -> bool
             end

            module PairSet :
             sig
              module Raw :
               sig
                type elt = nt_la_pair

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
                type t = nt_la_pair

                val eq_dec : nt_la_pair -> nt_la_pair -> bool
               end

              type elt = nt_la_pair

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

            module PairSetFacts :
             sig
              val eqb : nt_la_pair -> nt_la_pair -> bool
             end

            module PairSetEqProps :
             sig
              module MP :
               sig
                module Dec :
                 sig
                  module F :
                   sig
                    val eqb : nt_la_pair -> nt_la_pair -> bool
                   end

                  module MSetLogicalFacts :
                   sig
                   end

                  module MSetDecideAuxiliary :
                   sig
                   end

                  module MSetDecideTestCases :
                   sig
                   end
                 end

                module FM :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                val coq_In_dec : PairSet.elt -> PairSet.t -> bool

                val of_list : PairSet.elt list -> PairSet.t

                val to_list : PairSet.t -> PairSet.elt list

                val fold_rec :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  __ -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __
                  -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_bis :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt ->
                  'a1 -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_nodep :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                  (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_weak :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t ->
                  'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
                  PairSet.t -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

                val fold_rel :
                  (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1
                  -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ ->
                  'a3 -> 'a3) -> 'a3

                val set_induction :
                  (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                  PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

                val set_induction_bis :
                  (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
                  (PairSet.elt -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

                val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

                val cardinal_inv_2b : PairSet.t -> PairSet.elt
               end

              val choose_mem_3 : PairSet.t -> PairSet.elt

              val set_rec :
                (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t ->
                PairSet.elt -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

              val for_all_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

              val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

              val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
             end

            module PP :
             sig
              module Dec :
               sig
                module F :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                module MSetLogicalFacts :
                 sig
                 end

                module MSetDecideAuxiliary :
                 sig
                 end

                module MSetDecideTestCases :
                 sig
                 end
               end

              module FM :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              val coq_In_dec : PairSet.elt -> PairSet.t -> bool

              val of_list : PairSet.elt list -> PairSet.t

              val to_list : PairSet.t -> PairSet.elt list

              val fold_rec :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t -> __
                -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __ ->
                __ -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_bis :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1
                -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_nodep :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

              val fold_rec_weak :
                (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t ->
                'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 -> PairSet.t
                -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

              val fold_rel :
                (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1
                -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ ->
                'a3 -> 'a3) -> 'a3

              val set_induction :
                (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

              val set_induction_bis :
                (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (PairSet.elt
                -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

              val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

              val cardinal_inv_2b : PairSet.t -> PairSet.elt
             end

            module PD :
             sig
              module F :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              module MSetLogicalFacts :
               sig
               end

              module MSetDecideAuxiliary :
               sig
               end

              module MSetDecideTestCases :
               sig
               end
             end

            val mkPairs :
              G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

            val pairsOf : G.Defs.Specs.first_map -> PairSet.t

            val leftmostLookahead :
              G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

            val leftmostLookaheads' :
              G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

            val leftmostLookaheads :
              G.Defs.production list -> G.Defs.Collections.LaSet.t

            val product :
              G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t -> PairSet.t

            val numFirstCandidates :
              G.Defs.production list -> G.Defs.Specs.first_map -> nat

            val mkFirstMap'_func :
              (G.Defs.production list, (G.Defs.Collections.NtSet.t,
              (G.Defs.Specs.first_map, __) sigT) sigT) sigT ->
              G.Defs.Specs.first_map

            val mkFirstMap' :
              G.Defs.production list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Specs.first_map

            val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

            val mkFirstMap :
              G.Defs.grammar -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map

            val updateFo' :
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
              G.SymTy.nonterminal -> G.Defs.symbol list -> G.Defs.Specs.follow_map
              -> G.Defs.Specs.follow_map

            val updateFo :
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
              G.Defs.production -> G.Defs.Specs.follow_map ->
              G.Defs.Specs.follow_map

            val followPass :
              G.Defs.production list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
              G.Defs.Specs.follow_map

            val follow_map_equiv_dec :
              G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

            val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

            val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

            val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

            val lookaheadsOfGamma : G.Defs.symbol list -> G.Defs.Collections.LaSet.t

            val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

            val numFollowCandidates :
              G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

            val mkFollowMap'_func :
              (G.Defs.grammar, (G.Defs.Collections.NtSet.t,
              (G.Defs.Specs.first_map, (__, (G.Defs.Specs.follow_map, __) sigT)
              sigT) sigT) sigT) sigT -> G.Defs.Specs.follow_map

            val mkFollowMap' :
              G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
              G.Defs.Specs.follow_map

            val initial_fo :
              G.Defs.grammar -> G.Defs.Collections.LaSet.t
              G.Defs.Collections.NtMap.t

            val mkFollowMap :
              G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Specs.follow_map

            type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

            val fromLookaheadList :
              G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

            val firstGamma' :
              G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
              G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead list

            val firstEntries :
              G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map
              -> table_entry list

            val followLookahead :
              G.SymTy.nonterminal -> G.Defs.symbol list ->
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
              G.Defs.Lookahead.lookahead list

            val followEntries :
              G.Defs.xprod -> G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map
              -> table_entry list

            val entriesForProd :
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
              G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

            val mkEntries' :
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
              G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

            val mkEntries :
              G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
              G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

            val ambigMessage :
              G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol
              list -> G.Defs.symbol list -> char list

            val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

            val addEntry :
              table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
              (char list, G.Defs.Collections.parse_table) sum

            val mkParseTable :
              table_entry list -> (char list, G.Defs.Collections.parse_table) sum

            val dupMessage : G.Defs.production -> char list
           end

          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end
   end

  type pl_pair = G.Defs.production * G.Defs.Lookahead.lookahead

  val plPairOf :
    EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry ->
    G.Defs.production * G.Defs.Lookahead.lookahead

  val plPairsOf :
    EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry list ->
    (G.Defs.production * G.Defs.Lookahead.lookahead) list

  val pl_pair_eq_dec : pl_pair -> pl_pair -> bool
 end

module ParserSoundnessFn :
 functor (G:T) ->
 sig
  module ParserDefs :
   sig
    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end

    val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

    val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

    type sym_arg =
    | F_arg of G.Defs.symbol
    | G_arg of G.Defs.symbol list

    val sym_arg_rect :
      (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

    val sym_arg_rec :
      (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

    val sa_size : sym_arg -> nat

    val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

    val ptlk_dec :
      G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
      G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

    val meas :
      G.Defs.Collections.parse_table -> G.Defs.token list ->
      G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

    type parse_failure =
    | Reject of char list * G.Defs.token list
    | Error of char list * G.SymTy.nonterminal * G.Defs.token list

    val parse_failure_rect :
      (char list -> G.Defs.token list -> 'a1) -> (char list -> G.SymTy.nonterminal
      -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

    val parse_failure_rec :
      (char list -> G.Defs.token list -> 'a1) -> (char list -> G.SymTy.nonterminal
      -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

    val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

    type 'a length_lt_eq = bool

    val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

    val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

    val length_lt_eq_trans :
      'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1 length_lt_eq ->
      'a1 length_lt_eq

    val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

    val parseTree :
      G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
      G.Defs.Collections.NtSet.t -> (parse_failure,
      G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT) sum

    val parseForest :
      G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token list ->
      G.Defs.Collections.NtSet.t -> (parse_failure,
      G.Defs.rhs_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT) sum
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module ParserSafetyFn :
 functor (G:T) ->
 sig
  module ParserSoundness :
   sig
    module ParserDefs :
     sig
      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end

      val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

      val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

      type sym_arg =
      | F_arg of G.Defs.symbol
      | G_arg of G.Defs.symbol list

      val sym_arg_rect :
        (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

      val sym_arg_rec :
        (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

      val sa_size : sym_arg -> nat

      val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

      val ptlk_dec :
        G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
        G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

      val meas :
        G.Defs.Collections.parse_table -> G.Defs.token list ->
        G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

      type parse_failure =
      | Reject of char list * G.Defs.token list
      | Error of char list * G.SymTy.nonterminal * G.Defs.token list

      val parse_failure_rect :
        (char list -> G.Defs.token list -> 'a1) -> (char list ->
        G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

      val parse_failure_rec :
        (char list -> G.Defs.token list -> 'a1) -> (char list ->
        G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

      val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

      type 'a length_lt_eq = bool

      val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

      val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

      val length_lt_eq_trans :
        'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1 length_lt_eq ->
        'a1 length_lt_eq

      val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

      val parseTree :
        G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
        G.Defs.Collections.NtSet.t -> (parse_failure,
        G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT)
        sum

      val parseForest :
        G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token list
        -> G.Defs.Collections.NtSet.t -> (parse_failure,
        G.Defs.rhs_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT) sum
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module ParserProofsFn :
 functor (G:T) ->
 sig
  module ParserSafety :
   sig
    module ParserSoundness :
     sig
      module ParserDefs :
       sig
        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end

        val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

        val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

        type sym_arg =
        | F_arg of G.Defs.symbol
        | G_arg of G.Defs.symbol list

        val sym_arg_rect :
          (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

        val sym_arg_rec :
          (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

        val sa_size : sym_arg -> nat

        val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

        val ptlk_dec :
          G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
          G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

        val meas :
          G.Defs.Collections.parse_table -> G.Defs.token list ->
          G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

        type parse_failure =
        | Reject of char list * G.Defs.token list
        | Error of char list * G.SymTy.nonterminal * G.Defs.token list

        val parse_failure_rect :
          (char list -> G.Defs.token list -> 'a1) -> (char list ->
          G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

        val parse_failure_rec :
          (char list -> G.Defs.token list -> 'a1) -> (char list ->
          G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

        val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

        type 'a length_lt_eq = bool

        val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

        val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

        val length_lt_eq_trans :
          'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1 length_lt_eq
          -> 'a1 length_lt_eq

        val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

        val parseTree :
          G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
          G.Defs.Collections.NtSet.t -> (parse_failure,
          G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq)
          sigT) sum

        val parseForest :
          G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token list
          -> G.Defs.Collections.NtSet.t -> (parse_failure,
          G.Defs.rhs_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT)
          sum
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  module L :
   sig
    val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
   end
 end

module Coq0_Make :
 functor (G:T) ->
 sig
  module GeneratorAndProofs :
   sig
    module EntryProofs :
     sig
      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end

      module FollowProofs :
       sig
        module FirstProofs :
         sig
          module NullableProofs :
           sig
            module Gen :
             sig
              module L :
               sig
                val production_eq_dec :
                  G.Defs.production -> G.Defs.production -> bool
               end

              val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

              val nullableGamma :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

              val updateNu :
                G.Defs.production -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val nullablePass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val countNullableCandidates :
                G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

              val mkNullableSet'_func :
                (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
                G.Defs.Collections.NtSet.t

              val mkNullableSet' :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

              val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

              val findOrEmpty :
                G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
                G.Defs.Collections.LaSet.t

              val firstSym :
                G.Defs.symbol -> G.Defs.Specs.first_map ->
                G.Defs.Collections.LaSet.t

              val firstGamma :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

              val updateFi :
                G.Defs.Collections.NtSet.t -> G.Defs.production ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val firstPass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val first_map_equiv_dec :
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

              type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

              val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

              module MDT_Pair :
               sig
                type t = nt_la_pair

                val eq_dec : nt_la_pair -> nt_la_pair -> bool
               end

              module Pair_as_DT :
               sig
                type t = nt_la_pair

                val eq_dec : nt_la_pair -> nt_la_pair -> bool
               end

              module PairSet :
               sig
                module Raw :
                 sig
                  type elt = nt_la_pair

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
                  type t = nt_la_pair

                  val eq_dec : nt_la_pair -> nt_la_pair -> bool
                 end

                type elt = nt_la_pair

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

              module PairSetFacts :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              module PairSetEqProps :
               sig
                module MP :
                 sig
                  module Dec :
                   sig
                    module F :
                     sig
                      val eqb : nt_la_pair -> nt_la_pair -> bool
                     end

                    module MSetLogicalFacts :
                     sig
                     end

                    module MSetDecideAuxiliary :
                     sig
                     end

                    module MSetDecideTestCases :
                     sig
                     end
                   end

                  module FM :
                   sig
                    val eqb : nt_la_pair -> nt_la_pair -> bool
                   end

                  val coq_In_dec : PairSet.elt -> PairSet.t -> bool

                  val of_list : PairSet.elt list -> PairSet.t

                  val to_list : PairSet.t -> PairSet.elt list

                  val fold_rec :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t
                    -> __ -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t
                    -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_bis :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t
                    -> PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt
                    -> 'a1 -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_nodep :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                    (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_weak :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t
                    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
                    PairSet.t -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

                  val fold_rel :
                    (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) ->
                    'a1 -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 ->
                    __ -> 'a3 -> 'a3) -> 'a3

                  val set_induction :
                    (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                    PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

                  val set_induction_bis :
                    (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
                    (PairSet.elt -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t ->
                    'a1

                  val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

                  val cardinal_inv_2b : PairSet.t -> PairSet.elt
                 end

                val choose_mem_3 : PairSet.t -> PairSet.elt

                val set_rec :
                  (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t ->
                  PairSet.elt -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

                val for_all_mem_4 :
                  (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

                val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

                val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
               end

              module PP :
               sig
                module Dec :
                 sig
                  module F :
                   sig
                    val eqb : nt_la_pair -> nt_la_pair -> bool
                   end

                  module MSetLogicalFacts :
                   sig
                   end

                  module MSetDecideAuxiliary :
                   sig
                   end

                  module MSetDecideTestCases :
                   sig
                   end
                 end

                module FM :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                val coq_In_dec : PairSet.elt -> PairSet.t -> bool

                val of_list : PairSet.elt list -> PairSet.t

                val to_list : PairSet.t -> PairSet.elt list

                val fold_rec :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  __ -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __
                  -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_bis :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt ->
                  'a1 -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_nodep :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                  (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_weak :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t ->
                  'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
                  PairSet.t -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

                val fold_rel :
                  (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1
                  -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ ->
                  'a3 -> 'a3) -> 'a3

                val set_induction :
                  (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                  PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

                val set_induction_bis :
                  (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
                  (PairSet.elt -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

                val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

                val cardinal_inv_2b : PairSet.t -> PairSet.elt
               end

              module PD :
               sig
                module F :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                module MSetLogicalFacts :
                 sig
                 end

                module MSetDecideAuxiliary :
                 sig
                 end

                module MSetDecideTestCases :
                 sig
                 end
               end

              val mkPairs :
                G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

              val pairsOf : G.Defs.Specs.first_map -> PairSet.t

              val leftmostLookahead :
                G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

              val leftmostLookaheads' :
                G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

              val leftmostLookaheads :
                G.Defs.production list -> G.Defs.Collections.LaSet.t

              val product :
                G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t ->
                PairSet.t

              val numFirstCandidates :
                G.Defs.production list -> G.Defs.Specs.first_map -> nat

              val mkFirstMap'_func :
                (G.Defs.production list, (G.Defs.Collections.NtSet.t,
                (G.Defs.Specs.first_map, __) sigT) sigT) sigT ->
                G.Defs.Specs.first_map

              val mkFirstMap' :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

              val mkFirstMap :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map

              val updateFo' :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.SymTy.nonterminal -> G.Defs.symbol list ->
                G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

              val updateFo :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.production -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val followPass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val follow_map_equiv_dec :
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

              val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

              val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

              val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

              val lookaheadsOfGamma :
                G.Defs.symbol list -> G.Defs.Collections.LaSet.t

              val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

              val numFollowCandidates :
                G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

              val mkFollowMap'_func :
                (G.Defs.grammar, (G.Defs.Collections.NtSet.t,
                (G.Defs.Specs.first_map, (__, (G.Defs.Specs.follow_map, __) sigT)
                sigT) sigT) sigT) sigT -> G.Defs.Specs.follow_map

              val mkFollowMap' :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val initial_fo :
                G.Defs.grammar -> G.Defs.Collections.LaSet.t
                G.Defs.Collections.NtMap.t

              val mkFollowMap :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map

              type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

              val fromLookaheadList :
                G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

              val firstGamma' :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead list

              val firstEntries :
                G.Defs.xprod -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> table_entry list

              val followLookahead :
                G.SymTy.nonterminal -> G.Defs.symbol list ->
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
                G.Defs.Lookahead.lookahead list

              val followEntries :
                G.Defs.xprod -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.follow_map -> table_entry list

              val entriesForProd :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

              val mkEntries' :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

              val mkEntries :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

              val ambigMessage :
                G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol
                list -> G.Defs.symbol list -> char list

              val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

              val addEntry :
                table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
                (char list, G.Defs.Collections.parse_table) sum

              val mkParseTable :
                table_entry list -> (char list, G.Defs.Collections.parse_table) sum

              val dupMessage : G.Defs.production -> char list
             end

            module L :
             sig
              val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
             end
           end

          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end
     end

    type pl_pair = G.Defs.production * G.Defs.Lookahead.lookahead

    val plPairOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry ->
      G.Defs.production * G.Defs.Lookahead.lookahead

    val plPairsOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry list ->
      (G.Defs.production * G.Defs.Lookahead.lookahead) list

    val pl_pair_eq_dec : pl_pair -> pl_pair -> bool
   end

  module ParserAndProofs :
   sig
    module ParserSafety :
     sig
      module ParserSoundness :
       sig
        module ParserDefs :
         sig
          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end

          val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

          val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

          type sym_arg =
          | F_arg of G.Defs.symbol
          | G_arg of G.Defs.symbol list

          val sym_arg_rect :
            (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

          val sym_arg_rec :
            (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

          val sa_size : sym_arg -> nat

          val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

          val ptlk_dec :
            G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
            G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

          val meas :
            G.Defs.Collections.parse_table -> G.Defs.token list ->
            G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

          type parse_failure =
          | Reject of char list * G.Defs.token list
          | Error of char list * G.SymTy.nonterminal * G.Defs.token list

          val parse_failure_rect :
            (char list -> G.Defs.token list -> 'a1) -> (char list ->
            G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

          val parse_failure_rec :
            (char list -> G.Defs.token list -> 'a1) -> (char list ->
            G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

          val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

          type 'a length_lt_eq = bool

          val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

          val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

          val length_lt_eq_trans :
            'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1
            length_lt_eq -> 'a1 length_lt_eq

          val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

          val parseTree :
            G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
            G.Defs.Collections.NtSet.t -> (parse_failure,
            G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq)
            sigT) sum

          val parseForest :
            G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token
            list -> G.Defs.Collections.NtSet.t -> (parse_failure,
            G.Defs.rhs_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT)
            sum
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  val parseTableOf :
    G.Defs.grammar -> (char list, G.Defs.Collections.parse_table) sum

  val parse :
    G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
    (ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parse_failure,
    G.Defs.symbol_semty * G.Defs.token list) sum
 end

type jvalue =
| JAssoc of (char list * jvalue) list
| JBool of bool
| JFloat of nat
| JInt of nat
| JList of jvalue list
| JNull
| JString of char list

module Json_Types :
 sig
  type terminal' =
  | Int
  | Float
  | Str
  | Tru
  | Fls
  | Null
  | LeftBrace
  | RightBrace
  | LeftBrack
  | RightBrack
  | Colon
  | Comma

  val terminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> terminal' -> 'a1

  val terminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    'a1 -> terminal' -> 'a1

  type terminal = terminal'

  type nonterminal' =
  | Value
  | Pairs
  | PairsTl
  | Pair
  | Elts
  | EltsTl

  val nonterminal'_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal' -> 'a1

  val nonterminal'_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal' -> 'a1

  type nonterminal = nonterminal'

  val t_eq_dec : terminal -> terminal -> bool

  val nt_eq_dec : nonterminal -> nonterminal -> bool

  val show_t : terminal -> char list

  val show_nt : nonterminal -> char list

  type t_semty = __

  type nt_semty = __
 end

module G :
 sig
  module SymTy :
   sig
    type terminal' = Json_Types.terminal' =
    | Int
    | Float
    | Str
    | Tru
    | Fls
    | Null
    | LeftBrace
    | RightBrace
    | LeftBrack
    | RightBrack
    | Colon
    | Comma

    val terminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> terminal' -> 'a1

    val terminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> terminal' -> 'a1

    type terminal = terminal'

    type nonterminal' = Json_Types.nonterminal' =
    | Value
    | Pairs
    | PairsTl
    | Pair
    | Elts
    | EltsTl

    val nonterminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal' -> 'a1

    val nonterminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal' -> 'a1

    type nonterminal = nonterminal'

    val t_eq_dec : terminal -> terminal -> bool

    val nt_eq_dec : nonterminal -> nonterminal -> bool

    val show_t : terminal -> char list

    val show_nt : nonterminal -> char list

    type t_semty = __

    type nt_semty = __
   end

  module Defs :
   sig
    type symbol =
    | T of SymTy.terminal
    | NT of SymTy.nonterminal

    val symbol_rect :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1) -> symbol -> 'a1

    val symbol_rec :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1) -> symbol -> 'a1

    type production = SymTy.nonterminal * symbol list

    val symbol_eq_dec : symbol -> symbol -> bool

    val show_symbol : symbol -> char list

    val prependToAll : char list -> char list list -> char list

    val intersperse : char list -> char list list -> char list

    val show_rhs : symbol list -> char list

    val show_prod : production -> char list

    type symbol_semty = __

    type tuple = __

    type rhs_semty = tuple

    type action_ty = __

    type xprod = (production, action_ty) sigT

    type token = (SymTy.terminal, SymTy.t_semty) sigT

    type grammar = { start : SymTy.nonterminal; prods : xprod list }

    val start : grammar -> SymTy.nonterminal

    val prods : grammar -> xprod list

    module Tree :
     sig
      type tree =
      | Leaf of SymTy.terminal
      | Node of SymTy.nonterminal * tree list

      val tree_rect :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree list -> 'a1) -> tree
        -> 'a1

      val tree_rec :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree list -> 'a1) -> tree
        -> 'a1

      val isNode : tree -> bool

      val isLeaf : tree -> bool
     end

    module Lookahead :
     sig
      type lookahead =
      | LA of SymTy.terminal
      | EOF

      val lookahead_rect : (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

      val lookahead_rec : (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

      val show_lookahead : lookahead -> char list
     end

    module Collections :
     sig
      module MDT_NT :
       sig
        type t = SymTy.nonterminal

        val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NT_as_DT :
       sig
        type t = SymTy.nonterminal

        val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NtSet :
       sig
        module Raw :
         sig
          type elt = SymTy.nonterminal

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
          type t = SymTy.nonterminal

          val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        type elt = SymTy.nonterminal

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

      module NtMap :
       sig
        module Raw :
         sig
          module PX :
           sig
           end

          type key = SymTy.nonterminal

          type 'elt t = (SymTy.nonterminal * 'elt) list

          val empty : 'a1 t

          val is_empty : 'a1 t -> bool

          val mem : key -> 'a1 t -> bool

          type 'elt coq_R_mem =
          | R_mem_0 of 'elt t
          | R_mem_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_mem_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1
            coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_find_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
            option -> 'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_add_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt t * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1
            t -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_remove_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt t * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __ -> __
            -> __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> SymTy.nonterminal -> 'a1 -> (SymTy.nonterminal * 'a1) list -> __
            -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

          val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
            'a3 option
         end

        module E :
         sig
          type t = SymTy.nonterminal

          val eq_dec : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        type key = SymTy.nonterminal

        type 'elt slist =
          'elt Raw.t
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

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val lookahead_eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool

      module MDT_Lookahead :
       sig
        type t = Lookahead.lookahead

        val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module Lookahead_as_DT :
       sig
        type t = Lookahead.lookahead

        val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module LaSet :
       sig
        module Raw :
         sig
          type elt = Lookahead.lookahead

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
          type t = Lookahead.lookahead

          val eq_dec : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        type elt = Lookahead.lookahead

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

      type pt_key = SymTy.nonterminal * Lookahead.lookahead

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
          | R_mem_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
            -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> bool -> 'a1 coq_R_mem
            -> 'a2 -> 'a2) -> 'a1 t -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_mem_correct : key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_find_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
            'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 option -> 'a1
            coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1 option -> 'a1 coq_R_find ->
            'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_find_correct : key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_add_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
            -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1 coq_R_add
            -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_add_correct : key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list
          | R_remove_2 of 'elt t * pt_key * 'elt * (pt_key * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t -> 'a1
            coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t -> pt_key ->
            'a1 -> (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a1 t ->
            'a2

          val coq_R_remove_correct : key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * pt_key * 'elt * (pt_key * 'elt) list * 
             'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
            t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ -> 'a3) -> ('a1 t ->
            'a2 -> pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1
            t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2)
            coq_R_fold

          val check : ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool

          val submap : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list -> 'a3

          val combine : 'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2 option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list -> (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t ->
            (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
            'a3 option
         end

        module E :
         sig
          type t = pt_key

          val eq_dec : pt_key -> pt_key -> bool
         end

        type key = pt_key

        type 'elt slist =
          'elt Raw.t
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

        val map2 :
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      type first_map = LaSet.t NtMap.t

      type follow_map = LaSet.t NtMap.t

      type parse_table = xprod ParseTable.t
     end

    module CollectionFacts :
     sig
      module NtSetFacts :
       sig
        val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NtSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
           end

          val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

          val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

          val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

          val fold_rec :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
            Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
            'a2 -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
            Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 ->
            'a2) -> Collections.NtSet.t -> 'a2

          val fold_rel :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2
            -> 'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 ->
            (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
            Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
            -> Collections.NtSet.t -> 'a1

          val set_induction_bis :
            (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1
            -> (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1)
            -> Collections.NtSet.t -> 'a1

          val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

          val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
         end

        val choose_mem_3 : Collections.NtSet.t -> Collections.NtSet.elt

        val set_rec :
          (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          (Collections.NtSet.t -> Collections.NtSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.NtSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
          Collections.NtSet.elt

        val exists_mem_4 :
          (Collections.NtSet.elt -> bool) -> Collections.NtSet.t ->
          Collections.NtSet.elt

        val sum : (Collections.NtSet.elt -> nat) -> Collections.NtSet.t -> nat
       end

      module NtMapFacts :
       sig
        val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool

        val coq_In_dec : 'a1 Collections.NtMap.t -> Collections.NtMap.key -> bool
       end

      module LaSetFacts :
       sig
        val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module LaSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
             end

            module MSetLogicalFacts :
             sig
             end

            module MSetDecideAuxiliary :
             sig
             end

            module MSetDecideTestCases :
             sig
             end
           end

          module FM :
           sig
            val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
           end

          val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

          val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

          val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

          val fold_rec :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
            Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_bis :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ ->
            __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_nodep :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
            'a2 -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_weak :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
            Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 ->
            'a2) -> Collections.LaSet.t -> 'a2

          val fold_rel :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2
            -> 'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 ->
            (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

          val set_induction :
            (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
            Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
            -> Collections.LaSet.t -> 'a1

          val set_induction_bis :
            (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1
            -> (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1)
            -> Collections.LaSet.t -> 'a1

          val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

          val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
         end

        val choose_mem_3 : Collections.LaSet.t -> Collections.LaSet.elt

        val set_rec :
          (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          (Collections.LaSet.t -> Collections.LaSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.LaSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
          Collections.LaSet.elt

        val exists_mem_4 :
          (Collections.LaSet.elt -> bool) -> Collections.LaSet.t ->
          Collections.LaSet.elt

        val sum : (Collections.LaSet.elt -> nat) -> Collections.LaSet.t -> nat
       end

      module ParseTableFacts :
       sig
        val eqb : Collections.pt_key -> Collections.pt_key -> bool

        val coq_In_dec :
          'a1 Collections.ParseTable.t -> Collections.ParseTable.key -> bool
       end

      module NP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        val coq_In_dec : Collections.NtSet.elt -> Collections.NtSet.t -> bool

        val of_list : Collections.NtSet.elt list -> Collections.NtSet.t

        val to_list : Collections.NtSet.t -> Collections.NtSet.elt list

        val fold_rec :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> __ -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> Collections.NtSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          (Collections.NtSet.t -> Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.NtSet.t ->
          'a2 -> (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.NtSet.elt -> 'a1 -> Collections.NtSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.NtSet.t -> 'a2

        val fold_rel :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> (Collections.NtSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.NtSet.t -> 'a3 ->
          (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.NtSet.t -> __ -> 'a1) -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
          -> Collections.NtSet.t -> 'a1

        val set_induction_bis :
          (Collections.NtSet.t -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.NtSet.elt -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.NtSet.t -> 'a1

        val cardinal_inv_2 : Collections.NtSet.t -> nat -> Collections.NtSet.elt

        val cardinal_inv_2b : Collections.NtSet.t -> Collections.NtSet.elt
       end

      module ND :
       sig
        module F :
         sig
          val eqb : SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end

      module LP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
           end

          module MSetLogicalFacts :
           sig
           end

          module MSetDecideAuxiliary :
           sig
           end

          module MSetDecideTestCases :
           sig
           end
         end

        module FM :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        val coq_In_dec : Collections.LaSet.elt -> Collections.LaSet.t -> bool

        val of_list : Collections.LaSet.elt list -> Collections.LaSet.t

        val to_list : Collections.LaSet.t -> Collections.LaSet.elt list

        val fold_rec :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> __ -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> Collections.LaSet.t -> __ -> __ -> __ -> 'a2 ->
          'a2) -> 'a2

        val fold_rec_bis :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          (Collections.LaSet.t -> Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2 -> (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ ->
          __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_nodep :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> Collections.LaSet.t ->
          'a2 -> (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_weak :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.LaSet.elt -> 'a1 -> Collections.LaSet.t -> __ -> 'a2 -> 'a2)
          -> Collections.LaSet.t -> 'a2

        val fold_rel :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> (Collections.LaSet.elt -> 'a2 ->
          'a2) -> 'a1 -> 'a2 -> Collections.LaSet.t -> 'a3 ->
          (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

        val set_induction :
          (Collections.LaSet.t -> __ -> 'a1) -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
          -> Collections.LaSet.t -> 'a1

        val set_induction_bis :
          (Collections.LaSet.t -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) -> 'a1
          -> (Collections.LaSet.elt -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.LaSet.t -> 'a1

        val cardinal_inv_2 : Collections.LaSet.t -> nat -> Collections.LaSet.elt

        val cardinal_inv_2b : Collections.LaSet.t -> Collections.LaSet.elt
       end

      module LD :
       sig
        module F :
         sig
          val eqb : Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        module MSetLogicalFacts :
         sig
         end

        module MSetDecideAuxiliary :
         sig
         end

        module MSetDecideTestCases :
         sig
         end
       end
     end

    module Derivation :
     sig
      val peek : token list -> Lookahead.lookahead
     end

    module Utils :
     sig
      val isNT : symbol -> bool

      val isT : symbol -> bool

      val lhs : xprod -> SymTy.nonterminal

      val rhs : xprod -> symbol list

      val prodOf : xprod -> production

      val prodsOf : grammar -> production list

      val pt_lookup :
        SymTy.nonterminal -> Lookahead.lookahead -> Collections.parse_table ->
        xprod option

      val pt_add :
        SymTy.nonterminal -> Lookahead.lookahead -> xprod ->
        Collections.parse_table -> Collections.parse_table

      val fromNtList : SymTy.nonterminal list -> Collections.NtSet.t
     end

    module Specs :
     sig
      type first_map = Collections.LaSet.t Collections.NtMap.t

      type follow_map = Collections.LaSet.t Collections.NtMap.t
     end
   end
 end

module PG :
 sig
  module GeneratorAndProofs :
   sig
    module EntryProofs :
     sig
      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end

      module FollowProofs :
       sig
        module FirstProofs :
         sig
          module NullableProofs :
           sig
            module Gen :
             sig
              module L :
               sig
                val production_eq_dec :
                  G.Defs.production -> G.Defs.production -> bool
               end

              val lhSet : G.Defs.production list -> G.Defs.Collections.NtSet.t

              val nullableGamma :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool

              val updateNu :
                G.Defs.production -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val nullablePass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val countNullableCandidates :
                G.Defs.production list -> G.Defs.Collections.NtSet.t -> nat

              val mkNullableSet'_func :
                (G.Defs.production list, G.Defs.Collections.NtSet.t) sigT ->
                G.Defs.Collections.NtSet.t

              val mkNullableSet' :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Collections.NtSet.t

              val mkNullableSet : G.Defs.grammar -> G.Defs.Collections.NtSet.t

              val nullableSym : G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool

              val findOrEmpty :
                G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
                G.Defs.Collections.LaSet.t

              val firstSym :
                G.Defs.symbol -> G.Defs.Specs.first_map ->
                G.Defs.Collections.LaSet.t

              val firstGamma :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t

              val updateFi :
                G.Defs.Collections.NtSet.t -> G.Defs.production ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val firstPass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val first_map_equiv_dec :
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

              type nt_la_pair = G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

              val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool

              module MDT_Pair :
               sig
                type t = nt_la_pair

                val eq_dec : nt_la_pair -> nt_la_pair -> bool
               end

              module Pair_as_DT :
               sig
                type t = nt_la_pair

                val eq_dec : nt_la_pair -> nt_la_pair -> bool
               end

              module PairSet :
               sig
                module Raw :
                 sig
                  type elt = nt_la_pair

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
                  type t = nt_la_pair

                  val eq_dec : nt_la_pair -> nt_la_pair -> bool
                 end

                type elt = nt_la_pair

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

              module PairSetFacts :
               sig
                val eqb : nt_la_pair -> nt_la_pair -> bool
               end

              module PairSetEqProps :
               sig
                module MP :
                 sig
                  module Dec :
                   sig
                    module F :
                     sig
                      val eqb : nt_la_pair -> nt_la_pair -> bool
                     end

                    module MSetLogicalFacts :
                     sig
                     end

                    module MSetDecideAuxiliary :
                     sig
                     end

                    module MSetDecideTestCases :
                     sig
                     end
                   end

                  module FM :
                   sig
                    val eqb : nt_la_pair -> nt_la_pair -> bool
                   end

                  val coq_In_dec : PairSet.elt -> PairSet.t -> bool

                  val of_list : PairSet.elt list -> PairSet.t

                  val to_list : PairSet.t -> PairSet.elt list

                  val fold_rec :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t
                    -> __ -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t
                    -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_bis :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t
                    -> PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt
                    -> 'a1 -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_nodep :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                    (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

                  val fold_rec_weak :
                    (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t
                    -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
                    PairSet.t -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

                  val fold_rel :
                    (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) ->
                    'a1 -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 ->
                    __ -> 'a3 -> 'a3) -> 'a3

                  val set_induction :
                    (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                    PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

                  val set_induction_bis :
                    (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
                    (PairSet.elt -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t ->
                    'a1

                  val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

                  val cardinal_inv_2b : PairSet.t -> PairSet.elt
                 end

                val choose_mem_3 : PairSet.t -> PairSet.elt

                val set_rec :
                  (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> (PairSet.t ->
                  PairSet.elt -> __ -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a1

                val for_all_mem_4 :
                  (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

                val exists_mem_4 : (PairSet.elt -> bool) -> PairSet.t -> PairSet.elt

                val sum : (PairSet.elt -> nat) -> PairSet.t -> nat
               end

              module PP :
               sig
                module Dec :
                 sig
                  module F :
                   sig
                    val eqb : nt_la_pair -> nt_la_pair -> bool
                   end

                  module MSetLogicalFacts :
                   sig
                   end

                  module MSetDecideAuxiliary :
                   sig
                   end

                  module MSetDecideTestCases :
                   sig
                   end
                 end

                module FM :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                val coq_In_dec : PairSet.elt -> PairSet.t -> bool

                val of_list : PairSet.elt list -> PairSet.t

                val to_list : PairSet.t -> PairSet.elt list

                val fold_rec :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  __ -> 'a2) -> (PairSet.elt -> 'a1 -> PairSet.t -> PairSet.t -> __
                  -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_bis :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> (PairSet.t ->
                  PairSet.t -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt ->
                  'a1 -> PairSet.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_nodep :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> PairSet.t -> 'a2 ->
                  (PairSet.elt -> 'a1 -> __ -> 'a2 -> 'a2) -> 'a2

                val fold_rec_weak :
                  (PairSet.elt -> 'a1 -> 'a1) -> 'a1 -> (PairSet.t -> PairSet.t ->
                  'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (PairSet.elt -> 'a1 ->
                  PairSet.t -> __ -> 'a2 -> 'a2) -> PairSet.t -> 'a2

                val fold_rel :
                  (PairSet.elt -> 'a1 -> 'a1) -> (PairSet.elt -> 'a2 -> 'a2) -> 'a1
                  -> 'a2 -> PairSet.t -> 'a3 -> (PairSet.elt -> 'a1 -> 'a2 -> __ ->
                  'a3 -> 'a3) -> 'a3

                val set_induction :
                  (PairSet.t -> __ -> 'a1) -> (PairSet.t -> PairSet.t -> 'a1 ->
                  PairSet.elt -> __ -> __ -> 'a1) -> PairSet.t -> 'a1

                val set_induction_bis :
                  (PairSet.t -> PairSet.t -> __ -> 'a1 -> 'a1) -> 'a1 ->
                  (PairSet.elt -> PairSet.t -> __ -> 'a1 -> 'a1) -> PairSet.t -> 'a1

                val cardinal_inv_2 : PairSet.t -> nat -> PairSet.elt

                val cardinal_inv_2b : PairSet.t -> PairSet.elt
               end

              module PD :
               sig
                module F :
                 sig
                  val eqb : nt_la_pair -> nt_la_pair -> bool
                 end

                module MSetLogicalFacts :
                 sig
                 end

                module MSetDecideAuxiliary :
                 sig
                 end

                module MSetDecideTestCases :
                 sig
                 end
               end

              val mkPairs :
                G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t -> PairSet.t

              val pairsOf : G.Defs.Specs.first_map -> PairSet.t

              val leftmostLookahead :
                G.Defs.symbol list -> G.Defs.Lookahead.lookahead option

              val leftmostLookaheads' :
                G.Defs.symbol list list -> G.Defs.Collections.LaSet.t

              val leftmostLookaheads :
                G.Defs.production list -> G.Defs.Collections.LaSet.t

              val product :
                G.Defs.Collections.NtSet.t -> G.Defs.Collections.LaSet.t ->
                PairSet.t

              val numFirstCandidates :
                G.Defs.production list -> G.Defs.Specs.first_map -> nat

              val mkFirstMap'_func :
                (G.Defs.production list, (G.Defs.Collections.NtSet.t,
                (G.Defs.Specs.first_map, __) sigT) sigT) sigT ->
                G.Defs.Specs.first_map

              val mkFirstMap' :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map

              val empty_fi : G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t

              val mkFirstMap :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map

              val updateFo' :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.SymTy.nonterminal -> G.Defs.symbol list ->
                G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map

              val updateFo :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.production -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val followPass :
                G.Defs.production list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val follow_map_equiv_dec :
                G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool

              val ntsOfGamma : G.Defs.symbol list -> G.Defs.Collections.NtSet.t

              val ntsOfProd : G.Defs.production -> G.Defs.Collections.NtSet.t

              val ntsOf : G.Defs.grammar -> G.Defs.Collections.NtSet.t

              val lookaheadsOfGamma :
                G.Defs.symbol list -> G.Defs.Collections.LaSet.t

              val lookaheadsOf : G.Defs.grammar -> G.Defs.Collections.LaSet.t

              val numFollowCandidates :
                G.Defs.grammar -> G.Defs.Specs.follow_map -> nat

              val mkFollowMap'_func :
                (G.Defs.grammar, (G.Defs.Collections.NtSet.t,
                (G.Defs.Specs.first_map, (__, (G.Defs.Specs.follow_map, __) sigT)
                sigT) sigT) sigT) sigT -> G.Defs.Specs.follow_map

              val mkFollowMap' :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
                G.Defs.Specs.follow_map

              val initial_fo :
                G.Defs.grammar -> G.Defs.Collections.LaSet.t
                G.Defs.Collections.NtMap.t

              val mkFollowMap :
                G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Specs.follow_map

              type table_entry = G.Defs.xprod * G.Defs.Lookahead.lookahead

              val fromLookaheadList :
                G.Defs.xprod -> G.Defs.Lookahead.lookahead list -> table_entry list

              val firstGamma' :
                G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead list

              val firstEntries :
                G.Defs.xprod -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.first_map -> table_entry list

              val followLookahead :
                G.SymTy.nonterminal -> G.Defs.symbol list ->
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map ->
                G.Defs.Lookahead.lookahead list

              val followEntries :
                G.Defs.xprod -> G.Defs.Collections.NtSet.t ->
                G.Defs.Specs.follow_map -> table_entry list

              val entriesForProd :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.xprod -> table_entry list

              val mkEntries' :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.xprod list -> table_entry list

              val mkEntries :
                G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
                G.Defs.Specs.follow_map -> G.Defs.grammar -> table_entry list

              val ambigMessage :
                G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal -> G.Defs.symbol
                list -> G.Defs.symbol list -> char list

              val empty_table : G.Defs.xprod G.Defs.Collections.ParseTable.t

              val addEntry :
                table_entry -> (char list, G.Defs.Collections.parse_table) sum ->
                (char list, G.Defs.Collections.parse_table) sum

              val mkParseTable :
                table_entry list -> (char list, G.Defs.Collections.parse_table) sum

              val dupMessage : G.Defs.production -> char list
             end

            module L :
             sig
              val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
             end
           end

          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end
     end

    type pl_pair = G.Defs.production * G.Defs.Lookahead.lookahead

    val plPairOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry ->
      G.Defs.production * G.Defs.Lookahead.lookahead

    val plPairsOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry list ->
      (G.Defs.production * G.Defs.Lookahead.lookahead) list

    val pl_pair_eq_dec : pl_pair -> pl_pair -> bool
   end

  module ParserAndProofs :
   sig
    module ParserSafety :
     sig
      module ParserSoundness :
       sig
        module ParserDefs :
         sig
          module L :
           sig
            val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
           end

          val t_eq_dec : G.SymTy.terminal -> G.SymTy.terminal -> bool

          val nt_eq_dec : G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool

          type sym_arg =
          | F_arg of G.Defs.symbol
          | G_arg of G.Defs.symbol list

          val sym_arg_rect :
            (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

          val sym_arg_rec :
            (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1) -> sym_arg -> 'a1

          val sa_size : sym_arg -> nat

          val nt_keys : G.Defs.Collections.parse_table -> G.SymTy.nonterminal list

          val ptlk_dec :
            G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
            G.Defs.Collections.parse_table -> (__, G.Defs.xprod) sum

          val meas :
            G.Defs.Collections.parse_table -> G.Defs.token list ->
            G.Defs.Collections.NtSet.t -> sym_arg -> (nat * nat) * nat

          type parse_failure =
          | Reject of char list * G.Defs.token list
          | Error of char list * G.SymTy.nonterminal * G.Defs.token list

          val parse_failure_rect :
            (char list -> G.Defs.token list -> 'a1) -> (char list ->
            G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

          val parse_failure_rec :
            (char list -> G.Defs.token list -> 'a1) -> (char list ->
            G.SymTy.nonterminal -> G.Defs.token list -> 'a1) -> parse_failure -> 'a1

          val mem_dec : G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t -> bool

          type 'a length_lt_eq = bool

          val length_lt_eq_cons : 'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq

          val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq

          val length_lt_eq_trans :
            'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq -> 'a1
            length_lt_eq -> 'a1 length_lt_eq

          val mismatchMessage : G.SymTy.terminal -> G.SymTy.terminal -> char list

          val parseTree :
            G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
            G.Defs.Collections.NtSet.t -> (parse_failure,
            G.Defs.symbol_semty * (G.Defs.token list, G.Defs.token length_lt_eq)
            sigT) sum

          val parseForest :
            G.Defs.Collections.parse_table -> G.Defs.symbol list -> G.Defs.token
            list -> G.Defs.Collections.NtSet.t -> (parse_failure,
            G.Defs.rhs_semty * (G.Defs.token list, G.Defs.token length_lt_eq) sigT)
            sum
         end

        module L :
         sig
          val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
         end
       end

      module L :
       sig
        val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
       end
     end

    module L :
     sig
      val production_eq_dec : G.Defs.production -> G.Defs.production -> bool
     end
   end

  val parseTableOf :
    G.Defs.grammar -> (char list, G.Defs.Collections.parse_table) sum

  val parse :
    G.Defs.Collections.parse_table -> G.Defs.symbol -> G.Defs.token list ->
    (ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parse_failure,
    G.Defs.symbol_semty * G.Defs.token list) sum
 end

val jsonGrammar : G.Defs.grammar

type simply_typed_token =
| StInt of nat
| StFloat of nat
| StStr of char list
| StTru
| StFls
| StNull
| StLeftBrace
| StRightBrace
| StLeftBrack
| StRightBrack
| StColon
| StComma

val depTokenOfSimplyTypedToken : simply_typed_token -> G.Defs.token
