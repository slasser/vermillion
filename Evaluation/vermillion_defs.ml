
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> nat **)

let rec length = function
| [] -> O
| _ :: l' -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h



(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val flip : ('a1 -> 'a2 -> 'a3) -> 'a2 -> 'a1 -> 'a3 **)

let flip f x y =
  f y x

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

module Make_UDT =
 functor (M:MiniDecidableType) ->
 struct
  type t = M.t

  (** val eq_dec : t -> t -> bool **)

  let eq_dec =
    M.eq_dec
 end

module Nat =
 struct
  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n0 -> (match m with
               | O -> false
               | S m0 -> eq_dec n0 m0)
 end

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val list_eq_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eq_dec eq_dec0 l l' =
  match l with
  | [] -> (match l' with
           | [] -> true
           | _ :: _ -> false)
  | y :: l0 ->
    (match l' with
     | [] -> false
     | a0 :: l1 ->
       if eq_dec0 y a0
       then list_eq_dec eq_dec0 l0 l1
       else false)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val flat_map :
    ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t0 -> app (f x) (flat_map f t0)

(** val fold_left :
    ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val fold_right :
    ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t0 -> f b (fold_right f a0 t0)

(** val string_dec : char list -> char list -> bool **)

let rec string_dec s x =
  match s with
  | [] -> (match x with
           | [] -> true
           | _::_ -> false)
  | a::s0 ->
    (match x with
     | [] -> false
     | a0::s1 -> if (=) a a0 then string_dec s0 s1 else false)

module type Coq_DecidableType =
 DecidableTypeOrig

module KeyDecidableType =
 functor (D:Coq_DecidableType) ->
 struct
 end

module WFacts_fun =
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

  val map2 :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2
    t -> 'a3 t

  val elements : 'a1 t -> (key * 'a1) list

  val cardinal : 'a1 t -> nat

  val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
 end) ->
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false

  (** val coq_In_dec : 'a1 M.t -> M.key -> bool **)

  let coq_In_dec m x =
    let b = M.mem x m in if b then true else false
 end

module Raw =
 functor (X:Coq_DecidableType) ->
 struct
  module PX = KeyDecidableType(X)

  type key = X.t

  type 'elt t = (X.t * 'elt) list

  (** val empty : 'a1 t **)

  let empty =
    []

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | [] -> false
  | p :: l ->
    let (k', _) = p in if X.eq_dec k k' then true else mem k l

  type 'elt coq_R_mem =
  | R_mem_0 of 'elt t
  | R_mem_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_mem_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list * 
     bool * 'elt coq_R_mem

  (** val coq_R_mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ ->
      bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
      -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rect k f f0 f1 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l, _res, r0) ->
    f1 s k' _x l __ __ __ _res r0
      (coq_R_mem_rect k f f0 f1 l _res r0)

  (** val coq_R_mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ ->
      bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool
      -> 'a1 coq_R_mem -> 'a2 **)

  let rec coq_R_mem_rec k f f0 f1 _ _ = function
  | R_mem_0 s -> f s __
  | R_mem_1 (s, k', _x, l) -> f0 s k' _x l __ __ __
  | R_mem_2 (s, k', _x, l, _res, r0) ->
    f1 s k' _x l __ __ __ _res r0
      (coq_R_mem_rec k f f0 f1 l _res r0)

  (** val mem_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let rec mem_rect k f1 f0 f s =
    let f2 = f1 s in
    let f3 = f0 s in
    let f4 = f s in
    (match s with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f5 = f4 t0 e l __ in
       let f6 = fun _ _ ->
         let hrec = mem_rect k f1 f0 f l in f5 __ __ hrec
       in
       let f7 = f3 t0 e l __ in
       if X.eq_dec k t0 then f7 __ __ else f6 __ __)

  (** val mem_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let mem_rec =
    mem_rect

  (** val coq_R_mem_correct :
      key -> 'a1 t -> bool -> 'a1 coq_R_mem **)

  let coq_R_mem_correct k s _res =
    Obj.magic mem_rect k (fun y _ _ _ -> R_mem_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_mem_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_mem_2 (y, y0, y1, y2,
      (mem k y2), (y6 (mem k y2) __))) s _res __

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | [] -> None
  | p :: s' ->
    let (k', x) = p in
    if X.eq_dec k k' then Some x else find k s'

  type 'elt coq_R_find =
  | R_find_0 of 'elt t
  | R_find_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_find_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
     * 'elt option * 'elt coq_R_find

  (** val coq_R_find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1
      option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rect k f f0 f1 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s', _res, r0) ->
    f1 s k' x s' __ __ __ _res r0
      (coq_R_find_rect k f f0 f1 s' _res r0)

  (** val coq_R_find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1
      option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t -> 'a1
      option -> 'a1 coq_R_find -> 'a2 **)

  let rec coq_R_find_rec k f f0 f1 _ _ = function
  | R_find_0 s -> f s __
  | R_find_1 (s, k', x, s') -> f0 s k' x s' __ __ __
  | R_find_2 (s, k', x, s', _res, r0) ->
    f1 s k' x s' __ __ __ _res r0
      (coq_R_find_rec k f f0 f1 s' _res r0)

  (** val find_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let rec find_rect k f1 f0 f s =
    let f2 = f1 s in
    let f3 = f0 s in
    let f4 = f s in
    (match s with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f5 = f4 t0 e l __ in
       let f6 = fun _ _ ->
         let hrec = find_rect k f1 f0 f l in f5 __ __ hrec
       in
       let f7 = f3 t0 e l __ in
       if X.eq_dec k t0 then f7 __ __ else f6 __ __)

  (** val find_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let find_rec =
    find_rect

  (** val coq_R_find_correct :
      key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find **)

  let coq_R_find_correct k s _res =
    Obj.magic find_rect k (fun y _ _ _ -> R_find_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_find_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_find_2 (y, y0, y1,
      y2, (find k y2), (y6 (find k y2) __))) s _res __

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x = function
  | [] -> (k, x) :: []
  | p :: l ->
    let (k', y) = p in
    if X.eq_dec k k'
    then (k, x) :: l
    else (k', y) :: (add k x l)

  type 'elt coq_R_add =
  | R_add_0 of 'elt t
  | R_add_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_add_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
     * 'elt t * 'elt coq_R_add

  (** val coq_R_add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t ->
      'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
      ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
      __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t ->
      'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rect k x f f0 f1 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l, _res, r0) ->
    f1 s k' y l __ __ __ _res r0
      (coq_R_add_rect k x f f0 f1 l _res r0)

  (** val coq_R_add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t ->
      'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
      ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
      __ -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t ->
      'a1 t -> 'a1 coq_R_add -> 'a2 **)

  let rec coq_R_add_rec k x f f0 f1 _ _ = function
  | R_add_0 s -> f s __
  | R_add_1 (s, k', y, l) -> f0 s k' y l __ __ __
  | R_add_2 (s, k', y, l, _res, r0) ->
    f1 s k' y l __ __ __ _res r0
      (coq_R_add_rec k x f f0 f1 l _res r0)

  (** val add_rect :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t ->
      'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
      ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
      __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let rec add_rect k x f1 f0 f s =
    let f2 = f1 s in
    let f3 = f0 s in
    let f4 = f s in
    (match s with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f5 = f4 t0 e l __ in
       let f6 = fun _ _ ->
         let hrec = add_rect k x f1 f0 f l in f5 __ __ hrec
       in
       let f7 = f3 t0 e l __ in
       if X.eq_dec k t0 then f7 __ __ else f6 __ __)

  (** val add_rec :
      key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t ->
      'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) ->
      ('a1 t -> X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ ->
      __ -> 'a2 -> 'a2) -> 'a1 t -> 'a2 **)

  let add_rec =
    add_rect

  (** val coq_R_add_correct :
      key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add **)

  let coq_R_add_correct k x s _res =
    add_rect k x (fun y _ _ _ -> R_add_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_add_1 (y, y0, y1, y2))
      (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_add_2 (y, y0, y1, y2,
      (add k x y2), (y6 (add k x y2) __))) s _res __

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k = function
  | [] -> []
  | p :: l ->
    let (k', x) = p in
    if X.eq_dec k k' then l else (k', x) :: (remove k l)

  type 'elt coq_R_remove =
  | R_remove_0 of 'elt t
  | R_remove_1 of 'elt t * X.t * 'elt * (X.t * 'elt) list
  | R_remove_2 of 'elt t * X.t * 'elt * (X.t * 'elt) list
     * 'elt t * 'elt coq_R_remove

  (** val coq_R_remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1
      t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
      -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rect k f f0 f1 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l, _res, r0) ->
    f1 s k' x l __ __ __ _res r0
      (coq_R_remove_rect k f f0 f1 l _res r0)

  (** val coq_R_remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a1
      t -> 'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
      -> 'a1 coq_R_remove -> 'a2 **)

  let rec coq_R_remove_rec k f f0 f1 _ _ = function
  | R_remove_0 s -> f s __
  | R_remove_1 (s, k', x, l) -> f0 s k' x l __ __ __
  | R_remove_2 (s, k', x, l, _res, r0) ->
    f1 s k' x l __ __ __ _res r0
      (coq_R_remove_rec k f f0 f1 l _res r0)

  (** val remove_rect :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let rec remove_rect k f1 f0 f s =
    let f2 = f1 s in
    let f3 = f0 s in
    let f4 = f s in
    (match s with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f5 = f4 t0 e l __ in
       let f6 = fun _ _ ->
         let hrec = remove_rect k f1 f0 f l in f5 __ __ hrec
       in
       let f7 = f3 t0 e l __ in
       if X.eq_dec k t0 then f7 __ __ else f6 __ __)

  (** val remove_rec :
      key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> X.t -> 'a1 ->
      (X.t * 'a1) list -> __ -> __ -> __ -> 'a2) -> ('a1 t ->
      X.t -> 'a1 -> (X.t * 'a1) list -> __ -> __ -> __ -> 'a2
      -> 'a2) -> 'a1 t -> 'a2 **)

  let remove_rec =
    remove_rect

  (** val coq_R_remove_correct :
      key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove **)

  let coq_R_remove_correct k s _res =
    Obj.magic remove_rect k (fun y _ _ _ -> R_remove_0 y)
      (fun y y0 y1 y2 _ _ _ _ _ -> R_remove_1 (y, y0, y1,
      y2)) (fun y y0 y1 y2 _ _ _ y6 _ _ -> R_remove_2 (y, y0,
      y1, y2, (remove k y2), (y6 (remove k y2) __))) s _res __

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | [] -> acc
    | p :: m' -> let (k, e) = p in fold f m' (f k e acc)

  type ('elt, 'a) coq_R_fold =
  | R_fold_0 of 'elt t * 'a
  | R_fold_1 of 'elt t * 'a * X.t * 'elt * (X.t * 'elt) list
     * 'a * ('elt, 'a) coq_R_fold

  (** val coq_R_fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ ->
      'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) ->
      'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rect f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rect f f0 f1 m' (f k e acc) _res r0)

  (** val coq_R_fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ ->
      'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) ->
      'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 **)

  let rec coq_R_fold_rec f f0 f1 _ _ _ = function
  | R_fold_0 (m, acc) -> f0 m acc __
  | R_fold_1 (m, acc, k, e, m', _res, r0) ->
    f1 m acc k e m' __ _res r0
      (coq_R_fold_rec f f0 f1 m' (f k e acc) _res r0)

  (** val fold_rect :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ ->
      'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3 **)

  let rec fold_rect f1 f0 f m acc =
    let f2 = f0 m acc in
    let f3 = f m acc in
    (match m with
     | [] -> f2 __
     | p :: l ->
       let (t0, e) = p in
       let f4 = f3 t0 e l __ in
       let hrec = fold_rect f1 f0 f l (f1 t0 e acc) in f4 hrec)

  (** val fold_rec :
      (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __ ->
      'a3) -> ('a1 t -> 'a2 -> X.t -> 'a1 -> (X.t * 'a1) list
      -> __ -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3 **)

  let fold_rec =
    fold_rect

  (** val coq_R_fold_correct :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 ->
      ('a1, 'a2) coq_R_fold **)

  let coq_R_fold_correct f m acc _res =
    fold_rect f (fun y y0 _ _ _ -> R_fold_0 (y, y0))
      (fun y y0 y1 y2 y3 _ y5 _ _ -> R_fold_1 (y, y0, y1, y2,
      y3, (fold f y3 (f y1 y2 y0)),
      (y5 (fold f y3 (f y1 y2 y0)) __))) m acc _res __

  (** val check :
      ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t -> bool **)

  let check cmp k e m' =
    match find k m' with
    | Some e' -> cmp e e'
    | None -> false

  (** val submap :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let submap cmp m m' =
    fold (fun k e b -> (&&) (check cmp k e m') b) m true

  (** val equal :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    (&&) (submap cmp m m')
      (submap (fun e' e -> cmp e e') m' m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f e)) :: (map f m')

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | [] -> []
  | p :: m' -> let (k, e) = p in (k, (f k e)) :: (mapi f m')

  (** val combine_l :
      'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine_l m m' =
    mapi (fun k e -> ((Some e), (find k m'))) m

  (** val combine_r :
      'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine_r m m' =
    mapi (fun k e' -> ((find k m), (Some e'))) m'

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2) list
      -> 'a3 **)

  let fold_right_pair f =
    fold_right (fun p -> f (fst p) (snd p))

  (** val combine :
      'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t **)

  let combine m m' =
    let l = combine_l m m' in
    let r = combine_r m m' in fold_right_pair add r l

  (** val at_least_left :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option)
      option **)

  let at_least_left o o' =
    match o with
    | Some _ -> Some (o, o')
    | None -> None

  (** val at_least_right :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option)
      option **)

  let at_least_right o o' = match o' with
  | Some _ -> Some (o, o')
  | None -> None

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option * 'a2 option)
      option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (o, o')
    | None ->
      (match o' with
       | Some _ -> Some (o, o')
       | None -> None)

  (** val option_cons :
      key -> 'a1 option -> (key * 'a1) list -> (key * 'a1)
      list **)

  let option_cons k o l =
    match o with
    | Some e -> (k, e) :: l
    | None -> l

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> (key * 'a3) list **)

  let map2 f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p -> f (fst p) (snd p)) m0 in
    fold_right_pair option_cons [] m1

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option
      -> 'a2 option -> 'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module Make =
 functor (X:Coq_DecidableType) ->
 struct
  module Raw = Raw(X)

  module E = X

  type key = E.t

  type 'elt slist =
    'elt Raw.t
    (* singleton inductive, whose constructor was Build_slist *)

  (** val this : 'a1 slist -> 'a1 Raw.t **)

  let this s =
    s

  type 'elt t = 'elt slist

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty m =
    Raw.is_empty (this m)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add x e m =
    Raw.add x e (this m)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find x m =
    Raw.find x (this m)

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove x m =
    Raw.remove x (this m)

  (** val mem : key -> 'a1 t -> bool **)

  let mem x m =
    Raw.mem x (this m)

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    Raw.map f (this m)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi f m =
    Raw.mapi f (this m)

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t ->
      'a2 t -> 'a3 t **)

  let map2 f m m' =
    Raw.map2 f (this m) (this m')

  (** val elements : 'a1 t -> (key * 'a1) list **)

  let elements m =
    Raw.elements (this m)

  (** val cardinal : 'a1 t -> nat **)

  let cardinal m =
    length (this m)

  (** val fold :
      (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold f m i =
    Raw.fold f (this m) i

  (** val equal :
      ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal cmp m m' =
    Raw.equal cmp (this m) (this m')
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

module WFactsOn =
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
 struct
  (** val eqb : E.t -> E.t -> bool **)

  let eqb x y =
    if E.eq_dec x y then true else false
 end

module WDecideOn =
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
 struct
  module F = WFactsOn(E)(M)

  module MSetLogicalFacts =
   struct
   end

  module MSetDecideAuxiliary =
   struct
   end

  module MSetDecideTestCases =
   struct
   end
 end

module WPropertiesOn =
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
 struct
  module Dec = WDecideOn(E)(M)

  module FM = Dec.F

  (** val coq_In_dec : M.elt -> M.t -> bool **)

  let coq_In_dec x s =
    if M.mem x s then true else false

  (** val of_list : M.elt list -> M.t **)

  let of_list l =
    fold_right M.add M.empty l

  (** val to_list : M.t -> M.elt list **)

  let to_list =
    M.elements

  (** val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ ->
      'a2) -> (M.elt -> 'a1 -> M.t -> M.t -> __ -> __ -> __
      -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec f i s pempty pstep =
    let l = rev (M.elements s) in
    let pstep' = fun x a s' s'' x0 ->
      pstep x a s' s'' __ __ __ x0
    in
    let rec f0 l0 pstep'0 s0 =
      match l0 with
      | [] -> pempty s0 __
      | y :: l1 ->
        pstep'0 y (fold_right f i l1) (of_list l1) s0 __ __
          __
          (f0 l1 (fun x a0 s' s'' _ _ _ x0 ->
            pstep'0 x a0 s' s'' __ __ __ x0) (of_list l1))
    in f0 l (fun x a s' s'' _ _ _ x0 -> pstep' x a s' s'' x0)
         s

  (** val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t ->
      'a1 -> __ -> 'a2 -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t
      -> __ -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec_bis f i s pmorphism pempty pstep =
    fold_rec f i s (fun s' _ ->
      pmorphism M.empty s' i __ pempty)
      (fun x a s' s'' _ _ _ x0 ->
      pmorphism (M.add x s') s'' (f x a) __
        (pstep x a s' __ __ x0))

  (** val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt ->
      'a1 -> __ -> 'a2 -> 'a2) -> 'a2 **)

  let fold_rec_nodep f i s x x0 =
    fold_rec_bis f i s (fun _ _ _ _ x1 -> x1) x
      (fun x1 a _ _ _ x2 -> x0 x1 a __ x2)

  (** val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 ->
      __ -> 'a2 -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __
      -> 'a2 -> 'a2) -> M.t -> 'a2 **)

  let fold_rec_weak f i x x0 x1 s =
    fold_rec_bis f i s x x0 (fun x2 a s' _ _ x3 ->
      x1 x2 a s' __ x3)

  (** val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1
      -> 'a2 -> M.t -> 'a3 -> (M.elt -> 'a1 -> 'a2 -> __ ->
      'a3 -> 'a3) -> 'a3 **)

  let fold_rel f g0 i j s rempty rstep =
    let l = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 y (fold_right f i l1) (fold_right g0 j l1) __
          (f0 l1 (fun x a0 b _ x0 -> rstep'0 x a0 b __ x0))
    in f0 l (fun x a b _ x0 -> rstep' x a b x0)

  (** val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __
      -> __ -> 'a1) -> M.t -> 'a1 **)

  let set_induction x x0 s =
    fold_rec (fun _ _ -> ()) () s x
      (fun x1 _ s' s'' _ _ _ x2 -> x0 s' s'' x2 x1 __ __)

  (** val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt ->
      M.t -> __ -> 'a1 -> 'a1) -> M.t -> 'a1 **)

  let set_induction_bis x x0 x1 s =
    fold_rec_bis (fun _ _ -> ()) () s (fun s0 s' _ _ x2 ->
      x s0 s' __ x2) x0 (fun x2 _ s' _ _ x3 -> x1 x2 s' __ x3)

  (** val cardinal_inv_2 : M.t -> nat -> M.elt **)

  let cardinal_inv_2 s _ =
    let l = M.elements s in
    (match l with
     | [] -> assert false (* absurd case *)
     | e :: _ -> e)

  (** val cardinal_inv_2b : M.t -> M.elt **)

  let cardinal_inv_2b s =
    let n = M.cardinal s in
    let x = fun x -> cardinal_inv_2 s x in
    (match n with
     | O -> assert false (* absurd case *)
     | S n0 -> x n0)
 end

module WProperties =
 functor (M:WSets) ->
 WPropertiesOn(M.E)(M)

module Properties = WProperties

module WEqPropertiesOn =
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
 struct
  module MP = WPropertiesOn(E)(M)

  (** val choose_mem_3 : M.t -> M.elt **)

  let choose_mem_3 s =
    let o = M.choose s in
    (match o with
     | Some e -> e
     | None -> assert false (* absurd case *))

  (** val set_rec :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> (M.t -> M.elt -> __
      -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a1 **)

  let set_rec x x0 x1 s =
    MP.set_induction (fun s0 _ -> x M.empty s0 __ x1)
      (fun s0 s' x2 x3 _ _ ->
      x (M.add x3 s0) s' __ (x0 s0 x3 __ x2)) s

  (** val for_all_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let for_all_mem_4 f s =
    choose_mem_3 (M.filter (fun x -> negb (f x)) s)

  (** val exists_mem_4 : (M.elt -> bool) -> M.t -> M.elt **)

  let exists_mem_4 f s =
    for_all_mem_4 (fun x -> negb (f x)) s

  (** val sum : (M.elt -> nat) -> M.t -> nat **)

  let sum f s =
    M.fold (fun x -> add (f x)) s O
 end

module WEqProperties =
 functor (M:WSets) ->
 WEqPropertiesOn(M.E)(M)

module EqProperties = WEqProperties

module MakeRaw =
 functor (X:DecidableType) ->
 struct
  type elt = X.t

  type t = elt list

  (** val empty : t **)

  let empty =
    []

  (** val is_empty : t -> bool **)

  let is_empty = function
  | [] -> true
  | _ :: _ -> false

  (** val mem : elt -> t -> bool **)

  let rec mem x = function
  | [] -> false
  | y :: l -> if X.eq_dec x y then true else mem x l

  (** val add : elt -> t -> t **)

  let rec add x s = match s with
  | [] -> x :: []
  | y :: l -> if X.eq_dec x y then s else y :: (add x l)

  (** val singleton : elt -> t **)

  let singleton x =
    x :: []

  (** val remove : elt -> t -> t **)

  let rec remove x = function
  | [] -> []
  | y :: l -> if X.eq_dec x y then l else y :: (remove x l)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f =
    fold_left (flip f)

  (** val union : t -> t -> t **)

  let union s =
    fold add s

  (** val diff : t -> t -> t **)

  let diff s s' =
    fold remove s' s

  (** val inter : t -> t -> t **)

  let inter s s' =
    fold (fun x s0 -> if mem x s' then add x s0 else s0) s []

  (** val subset : t -> t -> bool **)

  let subset s s' =
    is_empty (diff s s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    (&&) (subset s s') (subset s' s)

  (** val filter : (elt -> bool) -> t -> t **)

  let rec filter f = function
  | [] -> []
  | x :: l -> if f x then x :: (filter f l) else filter f l

  (** val for_all : (elt -> bool) -> t -> bool **)

  let rec for_all f = function
  | [] -> true
  | x :: l -> if f x then for_all f l else false

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let rec exists_ f = function
  | [] -> false
  | x :: l -> if f x then true else exists_ f l

  (** val partition : (elt -> bool) -> t -> t * t **)

  let rec partition f = function
  | [] -> ([], [])
  | x :: l ->
    let (s1, s2) = partition f l in
    if f x then ((x :: s1), s2) else (s1, (x :: s2))

  (** val cardinal : t -> nat **)

  let cardinal =
    length

  (** val elements : t -> elt list **)

  let elements s =
    s

  (** val choose : t -> elt option **)

  let choose = function
  | [] -> None
  | x :: _ -> Some x

  (** val isok : elt list -> bool **)

  let rec isok = function
  | [] -> true
  | a :: l0 -> (&&) (negb (mem a l0)) (isok l0)
 end

module Coq_Make =
 functor (X:DecidableType) ->
 struct
  module Raw = MakeRaw(X)

  module E =
   struct
    type t = X.t

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      X.eq_dec
   end

  type elt = X.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  (** val this : t_ -> Raw.t **)

  let this t0 =
    t0

  type t = t_

  (** val mem : elt -> t -> bool **)

  let mem x s =
    Raw.mem x (this s)

  (** val add : elt -> t -> t **)

  let add x s =
    Raw.add x (this s)

  (** val remove : elt -> t -> t **)

  let remove x s =
    Raw.remove x (this s)

  (** val singleton : elt -> t **)

  let singleton =
    Raw.singleton

  (** val union : t -> t -> t **)

  let union s s' =
    Raw.union (this s) (this s')

  (** val inter : t -> t -> t **)

  let inter s s' =
    Raw.inter (this s) (this s')

  (** val diff : t -> t -> t **)

  let diff s s' =
    Raw.diff (this s) (this s')

  (** val equal : t -> t -> bool **)

  let equal s s' =
    Raw.equal (this s) (this s')

  (** val subset : t -> t -> bool **)

  let subset s s' =
    Raw.subset (this s) (this s')

  (** val empty : t **)

  let empty =
    Raw.empty

  (** val is_empty : t -> bool **)

  let is_empty s =
    Raw.is_empty (this s)

  (** val elements : t -> elt list **)

  let elements s =
    Raw.elements (this s)

  (** val choose : t -> elt option **)

  let choose s =
    Raw.choose (this s)

  (** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

  let fold f s =
    Raw.fold f (this s)

  (** val cardinal : t -> nat **)

  let cardinal s =
    Raw.cardinal (this s)

  (** val filter : (elt -> bool) -> t -> t **)

  let filter f s =
    Raw.filter f (this s)

  (** val for_all : (elt -> bool) -> t -> bool **)

  let for_all f s =
    Raw.for_all f (this s)

  (** val exists_ : (elt -> bool) -> t -> bool **)

  let exists_ f s =
    Raw.exists_ f (this s)

  (** val partition : (elt -> bool) -> t -> t * t **)

  let partition f s =
    let p = Raw.partition f (this s) in ((fst p), (snd p))

  (** val eq_dec : t -> t -> bool **)

  let eq_dec s0 s'0 =
    let b = Raw.equal s0 s'0 in if b then true else false
 end

module type SYMBOL_TYPES =
 sig
  type terminal

  type nonterminal

  type literal

  val t_eq_dec : terminal -> terminal -> bool

  val nt_eq_dec : nonterminal -> nonterminal -> bool
 end

module DefsFn =
 functor (SymTy:SYMBOL_TYPES) ->
 struct
  type symbol =
  | T of SymTy.terminal
  | NT of SymTy.nonterminal

  (** val symbol_rect :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1)
      -> symbol -> 'a1 **)

  let symbol_rect f f0 = function
  | T x -> f x
  | NT x -> f0 x

  (** val symbol_rec :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1)
      -> symbol -> 'a1 **)

  let symbol_rec f f0 = function
  | T x -> f x
  | NT x -> f0 x

  (** val symbol_eq_dec : symbol -> symbol -> bool **)

  let symbol_eq_dec s s' =
    match s with
    | T x ->
      (match s' with
       | T t0 -> SymTy.t_eq_dec x t0
       | NT _ -> false)
    | NT x ->
      (match s' with
       | T _ -> false
       | NT n0 -> SymTy.nt_eq_dec x n0)

  type production = SymTy.nonterminal * symbol list

  type token = SymTy.terminal * SymTy.literal

  type grammar = { start : SymTy.nonterminal;
                   prods : production list }

  (** val start : grammar -> SymTy.nonterminal **)

  let start g0 =
    g0.start

  (** val prods : grammar -> production list **)

  let prods g0 =
    g0.prods

  module Tree =
   struct
    type tree =
    | Leaf of SymTy.terminal
    | Node of SymTy.nonterminal * tree list

    (** val tree_rect :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree
        list -> 'a1) -> tree -> 'a1 **)

    let tree_rect f f0 = function
    | Leaf x -> f x
    | Node (x, x0) -> f0 x x0

    (** val tree_rec :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree
        list -> 'a1) -> tree -> 'a1 **)

    let tree_rec f f0 = function
    | Leaf x -> f x
    | Node (x, x0) -> f0 x x0

    (** val isNode : tree -> bool **)

    let isNode = function
    | Leaf _ -> false
    | Node (_, _) -> true

    (** val isLeaf : tree -> bool **)

    let isLeaf tr =
      negb (isNode tr)
   end

  module Lookahead =
   struct
    type lookahead =
    | LA of SymTy.terminal
    | EOF

    (** val lookahead_rect :
        (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1 **)

    let lookahead_rect f f0 = function
    | LA x -> f x
    | EOF -> f0

    (** val lookahead_rec :
        (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1 **)

    let lookahead_rec f f0 = function
    | LA x -> f x
    | EOF -> f0
   end

  module Collections =
   struct
    module MDT_NT =
     struct
      type t = SymTy.nonterminal

      (** val eq_dec :
          SymTy.nonterminal -> SymTy.nonterminal -> bool **)

      let eq_dec =
        SymTy.nt_eq_dec
     end

    module NT_as_DT = Make_UDT(MDT_NT)

    module NtSet = Coq_Make(NT_as_DT)

    module NtMap = Make(NT_as_DT)

    (** val lookahead_eq_dec :
        Lookahead.lookahead -> Lookahead.lookahead -> bool **)

    let lookahead_eq_dec lk lk2 =
      match lk with
      | Lookahead.LA x ->
        (match lk2 with
         | Lookahead.LA t0 -> SymTy.t_eq_dec x t0
         | Lookahead.EOF -> false)
      | Lookahead.EOF ->
        (match lk2 with
         | Lookahead.LA _ -> false
         | Lookahead.EOF -> true)

    module MDT_Lookahead =
     struct
      type t = Lookahead.lookahead

      (** val eq_dec :
          Lookahead.lookahead -> Lookahead.lookahead -> bool **)

      let eq_dec =
        lookahead_eq_dec
     end

    module Lookahead_as_DT = Make_UDT(MDT_Lookahead)

    module LaSet = Coq_Make(Lookahead_as_DT)

    type pt_key = SymTy.nonterminal * Lookahead.lookahead

    (** val pt_key_eq_dec : pt_key -> pt_key -> bool **)

    let pt_key_eq_dec k k2 =
      let (x, x0) = k in
      let (n, l) = k2 in
      if SymTy.nt_eq_dec x n
      then (match x0 with
            | Lookahead.LA x1 ->
              (match l with
               | Lookahead.LA t0 -> SymTy.t_eq_dec x1 t0
               | Lookahead.EOF -> false)
            | Lookahead.EOF ->
              (match l with
               | Lookahead.LA _ -> false
               | Lookahead.EOF -> true))
      else false

    module MDT_PtKey =
     struct
      type t = pt_key

      (** val eq_dec : pt_key -> pt_key -> bool **)

      let eq_dec =
        pt_key_eq_dec
     end

    module PtKey_as_DT = Make_UDT(MDT_PtKey)

    module ParseTable = Make(PtKey_as_DT)

    type first_map = LaSet.t NtMap.t

    type follow_map = LaSet.t NtMap.t

    type parse_table = symbol list ParseTable.t
   end

  module CollectionFacts =
   struct
    module NtSetFacts =
     WFactsOn(Collections.NT_as_DT)(Collections.NtSet)

    module NtSetEqProps = EqProperties(Collections.NtSet)

    module NtMapFacts =
     WFacts_fun(Collections.NT_as_DT)(Collections.NtMap)

    module LaSetFacts =
     WFactsOn(Collections.Lookahead_as_DT)(Collections.LaSet)

    module LaSetEqProps = EqProperties(Collections.LaSet)

    module ParseTableFacts =
     WFacts_fun(Collections.PtKey_as_DT)(Collections.ParseTable)

    module NP = Properties(Collections.NtSet)

    module ND =
     WDecideOn(Collections.NT_as_DT)(Collections.NtSet)

    module LP = Properties(Collections.LaSet)

    module LD =
     WDecideOn(Collections.Lookahead_as_DT)(Collections.LaSet)
   end

  module Derivation =
   struct
    (** val peek :
        SymTy.terminal list -> Lookahead.lookahead **)

    let peek = function
    | [] -> Lookahead.EOF
    | token0 :: _ -> Lookahead.LA token0
   end

  module Utils =
   struct
    (** val pt_lookup :
        SymTy.nonterminal -> Lookahead.lookahead ->
        Collections.parse_table -> symbol list option **)

    let pt_lookup x la tbl =
      Collections.ParseTable.find (x, la) tbl

    (** val pt_add :
        SymTy.nonterminal -> Lookahead.lookahead -> symbol
        list -> Collections.parse_table ->
        Collections.parse_table **)

    let pt_add x la gamma tbl =
      Collections.ParseTable.add (x, la) gamma tbl

    (** val isNT : symbol -> bool **)

    let isNT = function
    | T _ -> false
    | NT _ -> true

    (** val isT : symbol -> bool **)

    let isT = function
    | T _ -> true
    | NT _ -> false

    (** val fromNtList :
        SymTy.nonterminal list -> Collections.NtSet.t **)

    let fromNtList ls =
      fold_right Collections.NtSet.add
        Collections.NtSet.empty ls
   end

  module Specs =
   struct
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
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1)
      -> symbol -> 'a1

    val symbol_rec :
      (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> 'a1)
      -> symbol -> 'a1

    val symbol_eq_dec : symbol -> symbol -> bool

    type production = SymTy.nonterminal * symbol list

    type token = SymTy.terminal * SymTy.literal

    type grammar = { start : SymTy.nonterminal;
                     prods : production list }

    val start : grammar -> SymTy.nonterminal

    val prods : grammar -> production list

    module Tree :
     sig
      type tree =
      | Leaf of SymTy.terminal
      | Node of SymTy.nonterminal * tree list

      val tree_rect :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree
        list -> 'a1) -> tree -> 'a1

      val tree_rec :
        (SymTy.terminal -> 'a1) -> (SymTy.nonterminal -> tree
        list -> 'a1) -> tree -> 'a1

      val isNode : tree -> bool

      val isLeaf : tree -> bool
     end

    module Lookahead :
     sig
      type lookahead =
      | LA of SymTy.terminal
      | EOF

      val lookahead_rect :
        (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1

      val lookahead_rec :
        (SymTy.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1
     end

    module Collections :
     sig
      module MDT_NT :
       sig
        type t = SymTy.nonterminal

        val eq_dec :
          SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NT_as_DT :
       sig
        type t = SymTy.nonterminal

        val eq_dec :
          SymTy.nonterminal -> SymTy.nonterminal -> bool
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

          val eq_dec :
            SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        type elt = SymTy.nonterminal

        type t_ =
          Raw.t
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
             * (SymTy.nonterminal * 'elt) list * bool
             * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
            -> bool -> 'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> bool -> 'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t
            -> bool -> 'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct :
            key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * SymTy.nonterminal * 
             'elt * (SymTy.nonterminal * 'elt) list
          | R_find_2 of 'elt t * SymTy.nonterminal * 
             'elt * (SymTy.nonterminal * 'elt) list
             * 'elt option * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
            'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 option -> 'a1 coq_R_find -> 'a2 -> 'a2) ->
            'a1 t -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list
          | R_add_2 of 'elt t * SymTy.nonterminal * 'elt
             * (SymTy.nonterminal * 'elt) list * 'elt t
             * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
            -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t
            -> 'a1 t -> 'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * SymTy.nonterminal * 
             'elt * (SymTy.nonterminal * 'elt) list
          | R_remove_2 of 'elt t * SymTy.nonterminal * 
             'elt * (SymTy.nonterminal * 'elt) list * 
             'elt t * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a1 t -> 'a1 coq_R_remove -> 'a2 -> 'a2) ->
            'a1 t -> 'a1 t -> 'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> SymTy.nonterminal -> 'a1 ->
            (SymTy.nonterminal * 'a1) list -> __ -> __ -> __
            -> 'a2 -> 'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct :
            key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * SymTy.nonterminal
             * 'elt * (SymTy.nonterminal * 'elt) list * 
             'a * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ ->
            'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) ->
            'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold ->
            'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ ->
            'a2 -> ('a1, 'a2) coq_R_fold -> 'a3 -> 'a3) ->
            'a1 t -> 'a2 -> 'a2 -> ('a1, 'a2) coq_R_fold ->
            'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ ->
            'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> SymTy.nonterminal ->
            'a1 -> (SymTy.nonterminal * 'a1) list -> __ ->
            'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold

          val check :
            ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t ->
            bool

          val submap :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2)
            list -> 'a3

          val combine :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list ->
            (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t
            -> 'a2 t -> (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1
            option -> 'a2 option -> 'a3 option
         end

        module E :
         sig
          type t = SymTy.nonterminal

          val eq_dec :
            SymTy.nonterminal -> SymTy.nonterminal -> bool
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
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t
          -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      val lookahead_eq_dec :
        Lookahead.lookahead -> Lookahead.lookahead -> bool

      module MDT_Lookahead :
       sig
        type t = Lookahead.lookahead

        val eq_dec :
          Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module Lookahead_as_DT :
       sig
        type t = Lookahead.lookahead

        val eq_dec :
          Lookahead.lookahead -> Lookahead.lookahead -> bool
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

          val eq_dec :
            Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        type elt = Lookahead.lookahead

        type t_ =
          Raw.t
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
          | R_mem_1 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list
          | R_mem_2 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list * bool * 'elt coq_R_mem

          val coq_R_mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
            'a1 coq_R_mem -> 'a2

          val coq_R_mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> bool ->
            'a1 coq_R_mem -> 'a2 -> 'a2) -> 'a1 t -> bool ->
            'a1 coq_R_mem -> 'a2

          val mem_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val mem_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val coq_R_mem_correct :
            key -> 'a1 t -> bool -> 'a1 coq_R_mem

          val find : key -> 'a1 t -> 'a1 option

          type 'elt coq_R_find =
          | R_find_0 of 'elt t
          | R_find_1 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list
          | R_find_2 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list * 'elt option
             * 'elt coq_R_find

          val coq_R_find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t
            -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val coq_R_find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1
            option -> 'a1 coq_R_find -> 'a2 -> 'a2) -> 'a1 t
            -> 'a1 option -> 'a1 coq_R_find -> 'a2

          val find_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val find_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val coq_R_find_correct :
            key -> 'a1 t -> 'a1 option -> 'a1 coq_R_find

          val add : key -> 'a1 -> 'a1 t -> 'a1 t

          type 'elt coq_R_add =
          | R_add_0 of 'elt t
          | R_add_1 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list
          | R_add_2 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list * 'elt t * 'elt coq_R_add

          val coq_R_add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __
            -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
            'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_add -> 'a2

          val coq_R_add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __
            -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
            'a1 coq_R_add -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t ->
            'a1 coq_R_add -> 'a2

          val add_rect :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __
            -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val add_rec :
            key -> 'a1 -> ('a1 t -> __ -> 'a2) -> ('a1 t ->
            pt_key -> 'a1 -> (pt_key * 'a1) list -> __ -> __
            -> __ -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val coq_R_add_correct :
            key -> 'a1 -> 'a1 t -> 'a1 t -> 'a1 coq_R_add

          val remove : key -> 'a1 t -> 'a1 t

          type 'elt coq_R_remove =
          | R_remove_0 of 'elt t
          | R_remove_1 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list
          | R_remove_2 of 'elt t * pt_key * 'elt
             * (pt_key * 'elt) list * 'elt t
             * 'elt coq_R_remove

          val coq_R_remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_remove -> 'a2

          val coq_R_remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a1 t ->
            'a1 coq_R_remove -> 'a2 -> 'a2) -> 'a1 t -> 'a1 t
            -> 'a1 coq_R_remove -> 'a2

          val remove_rect :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val remove_rec :
            key -> ('a1 t -> __ -> 'a2) -> ('a1 t -> pt_key
            -> 'a1 -> (pt_key * 'a1) list -> __ -> __ -> __
            -> 'a2) -> ('a1 t -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> __ -> __ -> 'a2 ->
            'a2) -> 'a1 t -> 'a2

          val coq_R_remove_correct :
            key -> 'a1 t -> 'a1 t -> 'a1 coq_R_remove

          val elements : 'a1 t -> 'a1 t

          val fold :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

          type ('elt, 'a) coq_R_fold =
          | R_fold_0 of 'elt t * 'a
          | R_fold_1 of 'elt t * 'a * pt_key * 'elt
             * (pt_key * 'elt) list * 'a
             * ('elt, 'a) coq_R_fold

          val coq_R_fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val coq_R_fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> 'a2 -> ('a1, 'a2)
            coq_R_fold -> 'a3 -> 'a3) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold -> 'a3

          val fold_rect :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
            -> 'a2 -> 'a3

          val fold_rec :
            (key -> 'a1 -> 'a2 -> 'a2) -> ('a1 t -> 'a2 -> __
            -> 'a3) -> ('a1 t -> 'a2 -> pt_key -> 'a1 ->
            (pt_key * 'a1) list -> __ -> 'a3 -> 'a3) -> 'a1 t
            -> 'a2 -> 'a3

          val coq_R_fold_correct :
            (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
            -> ('a1, 'a2) coq_R_fold

          val check :
            ('a1 -> 'a1 -> bool) -> key -> 'a1 -> 'a1 t ->
            bool

          val submap :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val equal :
            ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

          val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

          val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

          val combine_l :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val combine_r :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val fold_right_pair :
            ('a1 -> 'a2 -> 'a3 -> 'a3) -> 'a3 -> ('a1 * 'a2)
            list -> 'a3

          val combine :
            'a1 t -> 'a2 t -> ('a1 option * 'a2 option) t

          val at_least_left :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val at_least_right :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val at_least_one :
            'a1 option -> 'a2 option -> ('a1 option * 'a2
            option) option

          val option_cons :
            key -> 'a1 option -> (key * 'a1) list ->
            (key * 'a1) list

          val map2 :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t
            -> 'a2 t -> (key * 'a3) list

          val at_least_one_then_f :
            ('a1 option -> 'a2 option -> 'a3 option) -> 'a1
            option -> 'a2 option -> 'a3 option
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
          ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t
          -> 'a2 t -> 'a3 t

        val elements : 'a1 t -> (key * 'a1) list

        val cardinal : 'a1 t -> nat

        val fold :
          (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

        val equal :
          ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool
       end

      type first_map = LaSet.t NtMap.t

      type follow_map = LaSet.t NtMap.t

      type parse_table = symbol list ParseTable.t
     end

    module CollectionFacts :
     sig
      module NtSetFacts :
       sig
        val eqb :
          SymTy.nonterminal -> SymTy.nonterminal -> bool
       end

      module NtSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb :
                SymTy.nonterminal -> SymTy.nonterminal -> bool
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
            val eqb :
              SymTy.nonterminal -> SymTy.nonterminal -> bool
           end

          val coq_In_dec :
            Collections.NtSet.elt -> Collections.NtSet.t ->
            bool

          val of_list :
            Collections.NtSet.elt list -> Collections.NtSet.t

          val to_list :
            Collections.NtSet.t -> Collections.NtSet.elt list

          val fold_rec :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.NtSet.t -> (Collections.NtSet.t -> __
            -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
            Collections.NtSet.t -> Collections.NtSet.t -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_bis :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.NtSet.t -> (Collections.NtSet.t ->
            Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.NtSet.elt -> 'a1 ->
            Collections.NtSet.t -> __ -> __ -> 'a2 -> 'a2) ->
            'a2

          val fold_rec_nodep :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.NtSet.t -> 'a2 ->
            (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_weak :
            (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            (Collections.NtSet.t -> Collections.NtSet.t ->
            'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.NtSet.elt -> 'a1 ->
            Collections.NtSet.t -> __ -> 'a2 -> 'a2) ->
            Collections.NtSet.t -> 'a2

          val fold_rel :
            (Collections.NtSet.elt -> 'a1 -> 'a1) ->
            (Collections.NtSet.elt -> 'a2 -> 'a2) -> 'a1 ->
            'a2 -> Collections.NtSet.t -> 'a3 ->
            (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3
            -> 'a3) -> 'a3

          val set_induction :
            (Collections.NtSet.t -> __ -> 'a1) ->
            (Collections.NtSet.t -> Collections.NtSet.t ->
            'a1 -> Collections.NtSet.elt -> __ -> __ -> 'a1)
            -> Collections.NtSet.t -> 'a1

          val set_induction_bis :
            (Collections.NtSet.t -> Collections.NtSet.t -> __
            -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.elt
            -> Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
            Collections.NtSet.t -> 'a1

          val cardinal_inv_2 :
            Collections.NtSet.t -> nat ->
            Collections.NtSet.elt

          val cardinal_inv_2b :
            Collections.NtSet.t -> Collections.NtSet.elt
         end

        val choose_mem_3 :
          Collections.NtSet.t -> Collections.NtSet.elt

        val set_rec :
          (Collections.NtSet.t -> Collections.NtSet.t -> __
          -> 'a1 -> 'a1) -> (Collections.NtSet.t ->
          Collections.NtSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.NtSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.NtSet.elt -> bool) ->
          Collections.NtSet.t -> Collections.NtSet.elt

        val exists_mem_4 :
          (Collections.NtSet.elt -> bool) ->
          Collections.NtSet.t -> Collections.NtSet.elt

        val sum :
          (Collections.NtSet.elt -> nat) ->
          Collections.NtSet.t -> nat
       end

      module NtMapFacts :
       sig
        val eqb :
          SymTy.nonterminal -> SymTy.nonterminal -> bool

        val coq_In_dec :
          'a1 Collections.NtMap.t -> Collections.NtMap.key ->
          bool
       end

      module LaSetFacts :
       sig
        val eqb :
          Lookahead.lookahead -> Lookahead.lookahead -> bool
       end

      module LaSetEqProps :
       sig
        module MP :
         sig
          module Dec :
           sig
            module F :
             sig
              val eqb :
                Lookahead.lookahead -> Lookahead.lookahead ->
                bool
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
            val eqb :
              Lookahead.lookahead -> Lookahead.lookahead ->
              bool
           end

          val coq_In_dec :
            Collections.LaSet.elt -> Collections.LaSet.t ->
            bool

          val of_list :
            Collections.LaSet.elt list -> Collections.LaSet.t

          val to_list :
            Collections.LaSet.t -> Collections.LaSet.elt list

          val fold_rec :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.LaSet.t -> (Collections.LaSet.t -> __
            -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
            Collections.LaSet.t -> Collections.LaSet.t -> __
            -> __ -> __ -> 'a2 -> 'a2) -> 'a2

          val fold_rec_bis :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.LaSet.t -> (Collections.LaSet.t ->
            Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2)
            -> 'a2 -> (Collections.LaSet.elt -> 'a1 ->
            Collections.LaSet.t -> __ -> __ -> 'a2 -> 'a2) ->
            'a2

          val fold_rec_nodep :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            Collections.LaSet.t -> 'a2 ->
            (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 ->
            'a2) -> 'a2

          val fold_rec_weak :
            (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
            (Collections.LaSet.t -> Collections.LaSet.t ->
            'a1 -> __ -> 'a2 -> 'a2) -> 'a2 ->
            (Collections.LaSet.elt -> 'a1 ->
            Collections.LaSet.t -> __ -> 'a2 -> 'a2) ->
            Collections.LaSet.t -> 'a2

          val fold_rel :
            (Collections.LaSet.elt -> 'a1 -> 'a1) ->
            (Collections.LaSet.elt -> 'a2 -> 'a2) -> 'a1 ->
            'a2 -> Collections.LaSet.t -> 'a3 ->
            (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3
            -> 'a3) -> 'a3

          val set_induction :
            (Collections.LaSet.t -> __ -> 'a1) ->
            (Collections.LaSet.t -> Collections.LaSet.t ->
            'a1 -> Collections.LaSet.elt -> __ -> __ -> 'a1)
            -> Collections.LaSet.t -> 'a1

          val set_induction_bis :
            (Collections.LaSet.t -> Collections.LaSet.t -> __
            -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.elt
            -> Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
            Collections.LaSet.t -> 'a1

          val cardinal_inv_2 :
            Collections.LaSet.t -> nat ->
            Collections.LaSet.elt

          val cardinal_inv_2b :
            Collections.LaSet.t -> Collections.LaSet.elt
         end

        val choose_mem_3 :
          Collections.LaSet.t -> Collections.LaSet.elt

        val set_rec :
          (Collections.LaSet.t -> Collections.LaSet.t -> __
          -> 'a1 -> 'a1) -> (Collections.LaSet.t ->
          Collections.LaSet.elt -> __ -> 'a1 -> 'a1) -> 'a1
          -> Collections.LaSet.t -> 'a1

        val for_all_mem_4 :
          (Collections.LaSet.elt -> bool) ->
          Collections.LaSet.t -> Collections.LaSet.elt

        val exists_mem_4 :
          (Collections.LaSet.elt -> bool) ->
          Collections.LaSet.t -> Collections.LaSet.elt

        val sum :
          (Collections.LaSet.elt -> nat) ->
          Collections.LaSet.t -> nat
       end

      module ParseTableFacts :
       sig
        val eqb :
          Collections.pt_key -> Collections.pt_key -> bool

        val coq_In_dec :
          'a1 Collections.ParseTable.t ->
          Collections.ParseTable.key -> bool
       end

      module NP :
       sig
        module Dec :
         sig
          module F :
           sig
            val eqb :
              SymTy.nonterminal -> SymTy.nonterminal -> bool
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
          val eqb :
            SymTy.nonterminal -> SymTy.nonterminal -> bool
         end

        val coq_In_dec :
          Collections.NtSet.elt -> Collections.NtSet.t -> bool

        val of_list :
          Collections.NtSet.elt list -> Collections.NtSet.t

        val to_list :
          Collections.NtSet.t -> Collections.NtSet.elt list

        val fold_rec :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.NtSet.t -> (Collections.NtSet.t -> __
          -> 'a2) -> (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> Collections.NtSet.t -> __ ->
          __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.NtSet.t -> (Collections.NtSet.t ->
          Collections.NtSet.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
          'a2 -> (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_nodep :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.NtSet.t -> 'a2 ->
          (Collections.NtSet.elt -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2

        val fold_rec_weak :
          (Collections.NtSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          (Collections.NtSet.t -> Collections.NtSet.t -> 'a1
          -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.NtSet.elt -> 'a1 ->
          Collections.NtSet.t -> __ -> 'a2 -> 'a2) ->
          Collections.NtSet.t -> 'a2

        val fold_rel :
          (Collections.NtSet.elt -> 'a1 -> 'a1) ->
          (Collections.NtSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
          -> Collections.NtSet.t -> 'a3 ->
          (Collections.NtSet.elt -> 'a1 -> 'a2 -> __ -> 'a3
          -> 'a3) -> 'a3

        val set_induction :
          (Collections.NtSet.t -> __ -> 'a1) ->
          (Collections.NtSet.t -> Collections.NtSet.t -> 'a1
          -> Collections.NtSet.elt -> __ -> __ -> 'a1) ->
          Collections.NtSet.t -> 'a1

        val set_induction_bis :
          (Collections.NtSet.t -> Collections.NtSet.t -> __
          -> 'a1 -> 'a1) -> 'a1 -> (Collections.NtSet.elt ->
          Collections.NtSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.NtSet.t -> 'a1

        val cardinal_inv_2 :
          Collections.NtSet.t -> nat -> Collections.NtSet.elt

        val cardinal_inv_2b :
          Collections.NtSet.t -> Collections.NtSet.elt
       end

      module ND :
       sig
        module F :
         sig
          val eqb :
            SymTy.nonterminal -> SymTy.nonterminal -> bool
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
            val eqb :
              Lookahead.lookahead -> Lookahead.lookahead ->
              bool
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
          val eqb :
            Lookahead.lookahead -> Lookahead.lookahead -> bool
         end

        val coq_In_dec :
          Collections.LaSet.elt -> Collections.LaSet.t -> bool

        val of_list :
          Collections.LaSet.elt list -> Collections.LaSet.t

        val to_list :
          Collections.LaSet.t -> Collections.LaSet.elt list

        val fold_rec :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.LaSet.t -> (Collections.LaSet.t -> __
          -> 'a2) -> (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> Collections.LaSet.t -> __ ->
          __ -> __ -> 'a2 -> 'a2) -> 'a2

        val fold_rec_bis :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.LaSet.t -> (Collections.LaSet.t ->
          Collections.LaSet.t -> 'a1 -> __ -> 'a2 -> 'a2) ->
          'a2 -> (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> __ -> __ -> 'a2 -> 'a2) ->
          'a2

        val fold_rec_nodep :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          Collections.LaSet.t -> 'a2 ->
          (Collections.LaSet.elt -> 'a1 -> __ -> 'a2 -> 'a2)
          -> 'a2

        val fold_rec_weak :
          (Collections.LaSet.elt -> 'a1 -> 'a1) -> 'a1 ->
          (Collections.LaSet.t -> Collections.LaSet.t -> 'a1
          -> __ -> 'a2 -> 'a2) -> 'a2 ->
          (Collections.LaSet.elt -> 'a1 ->
          Collections.LaSet.t -> __ -> 'a2 -> 'a2) ->
          Collections.LaSet.t -> 'a2

        val fold_rel :
          (Collections.LaSet.elt -> 'a1 -> 'a1) ->
          (Collections.LaSet.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2
          -> Collections.LaSet.t -> 'a3 ->
          (Collections.LaSet.elt -> 'a1 -> 'a2 -> __ -> 'a3
          -> 'a3) -> 'a3

        val set_induction :
          (Collections.LaSet.t -> __ -> 'a1) ->
          (Collections.LaSet.t -> Collections.LaSet.t -> 'a1
          -> Collections.LaSet.elt -> __ -> __ -> 'a1) ->
          Collections.LaSet.t -> 'a1

        val set_induction_bis :
          (Collections.LaSet.t -> Collections.LaSet.t -> __
          -> 'a1 -> 'a1) -> 'a1 -> (Collections.LaSet.elt ->
          Collections.LaSet.t -> __ -> 'a1 -> 'a1) ->
          Collections.LaSet.t -> 'a1

        val cardinal_inv_2 :
          Collections.LaSet.t -> nat -> Collections.LaSet.elt

        val cardinal_inv_2b :
          Collections.LaSet.t -> Collections.LaSet.elt
       end

      module LD :
       sig
        module F :
         sig
          val eqb :
            Lookahead.lookahead -> Lookahead.lookahead -> bool
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
      val peek : SymTy.terminal list -> Lookahead.lookahead
     end

    module Utils :
     sig
      val pt_lookup :
        SymTy.nonterminal -> Lookahead.lookahead ->
        Collections.parse_table -> symbol list option

      val pt_add :
        SymTy.nonterminal -> Lookahead.lookahead -> symbol
        list -> Collections.parse_table ->
        Collections.parse_table

      val isNT : symbol -> bool

      val isT : symbol -> bool

      val fromNtList :
        SymTy.nonterminal list -> Collections.NtSet.t
     end

    module Specs :
     sig
      type first_map = Collections.LaSet.t Collections.NtMap.t

      type follow_map =
        Collections.LaSet.t Collections.NtMap.t
     end
   end
 end

module LemmasFn =
 functor (G:T) ->
 struct
 end

module ParserFn =
 functor (G:T) ->
 struct
  module L = LemmasFn(G)

  (** val t_eq_dec :
      G.SymTy.terminal -> G.SymTy.terminal -> bool **)

  let t_eq_dec =
    G.SymTy.t_eq_dec

  (** val nt_eq_dec :
      G.SymTy.nonterminal -> G.SymTy.nonterminal -> bool **)

  let nt_eq_dec =
    G.SymTy.nt_eq_dec

  type sym_arg =
  | F_arg of G.Defs.symbol
  | G_arg of G.Defs.symbol list

  (** val sym_arg_rect :
      (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1)
      -> sym_arg -> 'a1 **)

  let sym_arg_rect f f0 = function
  | F_arg x -> f x
  | G_arg x -> f0 x

  (** val sym_arg_rec :
      (G.Defs.symbol -> 'a1) -> (G.Defs.symbol list -> 'a1)
      -> sym_arg -> 'a1 **)

  let sym_arg_rec f f0 = function
  | F_arg x -> f x
  | G_arg x -> f0 x

  (** val nt_keys :
      G.Defs.Collections.parse_table -> G.SymTy.nonterminal
      list **)

  let nt_keys tbl =
    map (fun pr -> let (y, _) = pr in let (x, _) = y in x)
      (G.Defs.Collections.ParseTable.elements tbl)

  (** val ptlk_dec :
      G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
      G.Defs.Collections.parse_table -> (__, G.Defs.symbol
      list) sum **)

  let ptlk_dec x la tbl =
    let o = G.Defs.Utils.pt_lookup x la tbl in
    (match o with
     | Some l -> Inr l
     | None -> Inl __)

  (** val meas :
      G.Defs.Collections.parse_table -> G.SymTy.terminal list
      -> G.Defs.Collections.NtSet.t -> sym_arg ->
      (nat * nat) * sym_arg **)

  let meas tbl word vis sa =
    (((length word),
      (G.Defs.Collections.NtSet.cardinal
        (G.Defs.Collections.NtSet.diff
          (G.Defs.Utils.fromNtList (nt_keys tbl)) vis))), sa)

  type parse_failure =
  | Reject of char list * G.SymTy.terminal list
  | LeftRec of G.SymTy.nonterminal
     * G.Defs.Collections.NtSet.t * G.SymTy.terminal list

  (** val parse_failure_rect :
      (char list -> G.SymTy.terminal list -> 'a1) ->
      (G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t ->
      G.SymTy.terminal list -> 'a1) -> parse_failure -> 'a1 **)

  let parse_failure_rect f f0 = function
  | Reject (x, x0) -> f x x0
  | LeftRec (x, x0, x1) -> f0 x x0 x1

  (** val parse_failure_rec :
      (char list -> G.SymTy.terminal list -> 'a1) ->
      (G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t ->
      G.SymTy.terminal list -> 'a1) -> parse_failure -> 'a1 **)

  let parse_failure_rec f f0 = function
  | Reject (x, x0) -> f x x0
  | LeftRec (x, x0, x1) -> f0 x x0 x1

  (** val mem_dec :
      G.SymTy.nonterminal -> G.Defs.Collections.NtSet.t ->
      bool **)

  let mem_dec x s =
    let b = G.Defs.Collections.NtSet.mem x s in
    if b then true else false

  type 'a length_lt_eq = bool

  (** val length_lt_eq_cons :
      'a1 list -> 'a1 -> 'a1 list -> 'a1 length_lt_eq **)

  let length_lt_eq_cons _ _ _ =
    true

  (** val length_lt_eq_refl : 'a1 list -> 'a1 length_lt_eq **)

  let length_lt_eq_refl _ =
    false

  (** val length_lt_eq_trans :
      'a1 list -> 'a1 list -> 'a1 list -> 'a1 length_lt_eq ->
      'a1 length_lt_eq -> 'a1 length_lt_eq **)

  let length_lt_eq_trans _ _ _ h h' =
    if h then true else h'

  (** val parseTree :
      G.Defs.Collections.parse_table -> G.Defs.symbol ->
      G.SymTy.terminal list -> G.Defs.Collections.NtSet.t ->
      (parse_failure, G.Defs.Tree.tree * (G.SymTy.terminal
      list, G.SymTy.terminal length_lt_eq) sigT) sum **)

  let rec parseTree tbl sym input vis =
    match sym with
    | G.Defs.T a ->
      (match input with
       | [] ->
         Inl (Reject
           (('i'::('n'::('p'::('u'::('t'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::[]))))))))))))))),
           input))
       | token0 :: input' ->
         if t_eq_dec a token0
         then Inr ((G.Defs.Tree.Leaf a), (ExistT (input',
                (length_lt_eq_cons input token0 input'))))
         else Inl (Reject
                (('t'::('o'::('k'::('e'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[])))))))))))))),
                input)))
    | G.Defs.NT x ->
      (match ptlk_dec x (G.Defs.Derivation.peek input) tbl with
       | Inl _ ->
         Inl (Reject
           (('l'::('o'::('o'::('k'::('u'::('p'::(' '::('f'::('a'::('i'::('l'::('u'::('r'::('e'::[])))))))))))))),
           input))
       | Inr s ->
         if mem_dec x vis
         then Inl (LeftRec (x, vis, input))
         else (match parseForest_nf tbl s input
                       (G.Defs.Collections.NtSet.add x vis) with
               | Inl pfail -> Inl pfail
               | Inr p ->
                 let (sts, s0) = p in
                 Inr ((G.Defs.Tree.Node (x, sts)), s0)))

  (** val parseForest_nf :
      G.Defs.Collections.parse_table -> G.Defs.symbol list ->
      G.SymTy.terminal list -> G.Defs.Collections.NtSet.t ->
      (parse_failure, G.Defs.Tree.tree
      list * (G.SymTy.terminal list, G.SymTy.terminal
      length_lt_eq) sigT) sum **)

  and parseForest_nf tbl gamma input vis =
    match gamma with
    | [] ->
      Inr ([], (ExistT (input, (length_lt_eq_refl input))))
    | sym :: gamma' ->
      (match parseTree tbl sym input vis with
       | Inl pfail -> Inl pfail
       | Inr p ->
         let (lSib, s) = p in
         let ExistT (input', hle) = s in
         if hle
         then (match parseForest_nf tbl gamma' input'
                       G.Defs.Collections.NtSet.empty with
               | Inl pfail -> Inl pfail
               | Inr p0 ->
                 let (rSibs, s0) = p0 in
                 let ExistT (input'', hle'') = s0 in
                 Inr ((lSib :: rSibs), (ExistT (input'',
                 (length_lt_eq_trans input'' input' input
                   hle'' hle)))))
         else (match parseForest_nf tbl gamma' input vis with
               | Inl pfail -> Inl pfail
               | Inr p0 ->
                 let (rSibs, s0) = p0 in
                 Inr ((lSib :: rSibs), s0)))

  (** val sa_size : sym_arg -> nat **)

  let sa_size = function
  | F_arg _ -> O
  | G_arg gamma -> add (S O) (length gamma)

  (** val parse_wrapper :
      G.Defs.Collections.parse_table -> G.Defs.symbol ->
      G.SymTy.terminal list -> (parse_failure,
      G.Defs.Tree.tree * (G.SymTy.terminal list,
      G.SymTy.terminal length_lt_eq) sigT) sum **)

  let parse_wrapper tbl sym input =
    parseTree tbl sym input G.Defs.Collections.NtSet.empty
 end

module GeneratorFn =
 functor (G:T) ->
 struct
  module L = LemmasFn(G)

  (** val lhSet :
      G.Defs.production list -> G.Defs.Collections.NtSet.t **)

  let lhSet ps =
    G.Defs.Utils.fromNtList (map fst ps)

  (** val nullableGamma :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t -> bool **)

  let rec nullableGamma gamma nu =
    match gamma with
    | [] -> true
    | s :: gamma' ->
      (match s with
       | G.Defs.T _ -> false
       | G.Defs.NT x ->
         if G.Defs.Collections.NtSet.mem x nu
         then nullableGamma gamma' nu
         else false)

  (** val updateNu :
      G.Defs.production -> G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.NtSet.t **)

  let updateNu p nu =
    let (x, gamma) = p in
    if nullableGamma gamma nu
    then G.Defs.Collections.NtSet.add x nu
    else nu

  (** val nullablePass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.NtSet.t **)

  let nullablePass ps nu =
    fold_right updateNu nu ps

  (** val countNullableCandidates :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      nat **)

  let countNullableCandidates ps nu =
    let candidates = lhSet ps in
    G.Defs.Collections.NtSet.cardinal
      (G.Defs.Collections.NtSet.diff candidates nu)

  (** val mkNullableSet'_func :
      (G.Defs.production list, G.Defs.Collections.NtSet.t)
      sigT -> G.Defs.Collections.NtSet.t **)

  let rec mkNullableSet'_func x =
    let ps = projT1 x in
    let nu = projT2 x in
    let mkNullableSet'0 = fun ps0 nu0 ->
      mkNullableSet'_func (ExistT (ps0, nu0))
    in
    let nu' = nullablePass ps nu in
    if G.Defs.Collections.NtSet.eq_dec nu nu'
    then nu
    else mkNullableSet'0 ps nu'

  (** val mkNullableSet' :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.NtSet.t **)

  let mkNullableSet' ps nu =
    mkNullableSet'_func (ExistT (ps, nu))

  (** val mkNullableSet :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t **)

  let mkNullableSet g0 =
    mkNullableSet' (G.Defs.prods g0)
      G.Defs.Collections.NtSet.empty

  (** val nullableSym :
      G.Defs.symbol -> G.Defs.Collections.NtSet.t -> bool **)

  let nullableSym sym nu =
    match sym with
    | G.Defs.T _ -> false
    | G.Defs.NT x -> G.Defs.Collections.NtSet.mem x nu

  (** val findOrEmpty :
      G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t **)

  let findOrEmpty x fi =
    match G.Defs.Collections.NtMap.find x fi with
    | Some s -> s
    | None -> G.Defs.Collections.LaSet.empty

  (** val firstSym :
      G.Defs.symbol -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t **)

  let firstSym sym fi =
    match sym with
    | G.Defs.T y ->
      G.Defs.Collections.LaSet.singleton (G.Defs.Lookahead.LA
        y)
    | G.Defs.NT x -> findOrEmpty x fi

  (** val firstGamma :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Collections.LaSet.t **)

  let rec firstGamma gamma nu fi =
    match gamma with
    | [] -> G.Defs.Collections.LaSet.empty
    | sym :: gamma' ->
      if nullableSym sym nu
      then G.Defs.Collections.LaSet.union (firstSym sym fi)
             (firstGamma gamma' nu fi)
      else firstSym sym fi

  (** val updateFi :
      G.Defs.Collections.NtSet.t -> G.Defs.production ->
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map **)

  let updateFi nu p fi =
    let (x, gamma) = p in
    let fg = firstGamma gamma nu fi in
    let xFirst = findOrEmpty x fi in
    let xFirst' = G.Defs.Collections.LaSet.union fg xFirst in
    if G.Defs.Collections.LaSet.eq_dec xFirst xFirst'
    then fi
    else G.Defs.Collections.NtMap.add x xFirst' fi

  (** val firstPass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map **)

  let firstPass ps nu fi =
    fold_right (updateFi nu) fi ps

  (** val first_map_equiv_dec :
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool **)

  let first_map_equiv_dec m m' =
    let b =
      G.Defs.Collections.NtMap.equal
        G.Defs.Collections.LaSet.equal m m'
    in
    if b then true else false

  type nt_la_pair =
    G.SymTy.nonterminal * G.Defs.Lookahead.lookahead

  (** val pair_eq_dec : nt_la_pair -> nt_la_pair -> bool **)

  let pair_eq_dec p p' =
    let (x, x0) = p in
    let (n, l) = p' in
    if G.SymTy.nt_eq_dec x n
    then G.Defs.Lookahead.lookahead_rect (fun t0 x1 ->
           match x1 with
           | G.Defs.Lookahead.LA t1 -> G.SymTy.t_eq_dec t0 t1
           | G.Defs.Lookahead.EOF -> false) (fun x1 ->
           match x1 with
           | G.Defs.Lookahead.LA _ -> false
           | G.Defs.Lookahead.EOF -> true) x0 l
    else false

  module MDT_Pair =
   struct
    type t = nt_la_pair

    (** val eq_dec : nt_la_pair -> nt_la_pair -> bool **)

    let eq_dec =
      pair_eq_dec
   end

  module Pair_as_DT = Make_UDT(MDT_Pair)

  module PairSet = Coq_Make(Pair_as_DT)

  module PairSetFacts = WFactsOn(Pair_as_DT)(PairSet)

  module PairSetEqProps = EqProperties(PairSet)

  module PP = Properties(PairSet)

  module PD = WDecideOn(Pair_as_DT)(PairSet)

  (** val mkPairs :
      G.SymTy.nonterminal -> G.Defs.Collections.LaSet.t ->
      PairSet.t **)

  let mkPairs x laSet =
    fold_right (fun la acc -> PairSet.add (x, la) acc)
      PairSet.empty (G.Defs.Collections.LaSet.elements laSet)

  (** val pairsOf : G.Defs.Specs.first_map -> PairSet.t **)

  let pairsOf fi =
    fold_right (fun p acc ->
      let (x, s) = p in PairSet.union (mkPairs x s) acc)
      PairSet.empty (G.Defs.Collections.NtMap.elements fi)

  (** val leftmostLookahead :
      G.Defs.symbol list -> G.Defs.Lookahead.lookahead option **)

  let rec leftmostLookahead = function
  | [] -> None
  | s :: gamma' ->
    (match s with
     | G.Defs.T y -> Some (G.Defs.Lookahead.LA y)
     | G.Defs.NT _ -> leftmostLookahead gamma')

  (** val leftmostLookaheads' :
      G.Defs.symbol list list -> G.Defs.Collections.LaSet.t **)

  let leftmostLookaheads' gammas =
    fold_right (fun gamma acc ->
      match leftmostLookahead gamma with
      | Some la -> G.Defs.Collections.LaSet.add la acc
      | None -> acc) G.Defs.Collections.LaSet.empty gammas

  (** val leftmostLookaheads :
      G.Defs.production list -> G.Defs.Collections.LaSet.t **)

  let leftmostLookaheads ps =
    leftmostLookaheads' (map snd ps)

  (** val product :
      G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.LaSet.t -> PairSet.t **)

  let product n l =
    let f = fun x acc -> PairSet.union (mkPairs x l) acc in
    G.Defs.Collections.NtSet.fold f n PairSet.empty

  (** val numFirstCandidates :
      G.Defs.production list -> G.Defs.Specs.first_map -> nat **)

  let numFirstCandidates ps fi =
    let allCandidates =
      product (lhSet ps) (leftmostLookaheads ps)
    in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fi))

  (** val mkFirstMap'_func :
      (G.Defs.production list, (G.Defs.Collections.NtSet.t,
      (G.Defs.Specs.first_map, __) sigT) sigT) sigT ->
      G.Defs.Specs.first_map **)

  let rec mkFirstMap'_func x =
    let ps = projT1 x in
    let nu = projT1 (projT2 x) in
    let fi = projT1 (projT2 (projT2 x)) in
    let mkFirstMap'0 = fun ps0 nu0 fi0 ->
      mkFirstMap'_func (ExistT (ps0, (ExistT (nu0, (ExistT
        (fi0, __))))))
    in
    let fi' = firstPass ps nu fi in
    if first_map_equiv_dec fi fi'
    then fi
    else mkFirstMap'0 ps nu fi'

  (** val mkFirstMap' :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map **)

  let mkFirstMap' ps nu fi =
    mkFirstMap'_func (ExistT (ps, (ExistT (nu, (ExistT (fi,
      __))))))

  (** val empty_fi :
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t **)

  let empty_fi =
    G.Defs.Collections.NtMap.empty

  (** val mkFirstMap :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map **)

  let mkFirstMap g0 nu =
    let ps = G.Defs.prods g0 in mkFirstMap' ps nu empty_fi

  (** val updateFo' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.SymTy.nonterminal -> G.Defs.symbol list ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map **)

  let rec updateFo' nu fi lx gamma fo =
    match gamma with
    | [] -> fo
    | s :: gamma' ->
      (match s with
       | G.Defs.T _ -> updateFo' nu fi lx gamma' fo
       | G.Defs.NT rx ->
         let fo' = updateFo' nu fi lx gamma' fo in
         let lSet = findOrEmpty lx fo' in
         let rSet = firstGamma gamma' nu fi in
         let additions =
           if nullableGamma gamma' nu
           then G.Defs.Collections.LaSet.union lSet rSet
           else rSet
         in
         (match G.Defs.Collections.NtMap.find rx fo' with
          | Some rxFollow ->
            if G.Defs.Collections.LaSet.subset additions
                 rxFollow
            then fo'
            else let rxFollow' =
                   G.Defs.Collections.LaSet.union rxFollow
                     additions
                 in
                 G.Defs.Collections.NtMap.add rx rxFollow' fo'
          | None ->
            if G.Defs.Collections.LaSet.is_empty additions
            then fo'
            else G.Defs.Collections.NtMap.add rx additions fo'))

  (** val updateFo :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.production -> G.Defs.Specs.follow_map ->
      G.Defs.Specs.follow_map **)

  let updateFo nu fi p fo =
    let (x, gamma) = p in updateFo' nu fi x gamma fo

  (** val followPass :
      G.Defs.production list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
      G.Defs.Specs.follow_map **)

  let followPass ps nu fi fo =
    fold_right (updateFo nu fi) fo ps

  (** val follow_map_equiv_dec :
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool **)

  let follow_map_equiv_dec =
    first_map_equiv_dec

  (** val ntsOfGamma :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t **)

  let rec ntsOfGamma = function
  | [] -> G.Defs.Collections.NtSet.empty
  | s :: gamma' ->
    (match s with
     | G.Defs.T _ -> ntsOfGamma gamma'
     | G.Defs.NT x ->
       G.Defs.Collections.NtSet.add x (ntsOfGamma gamma'))

  (** val ntsOfProd :
      G.Defs.production -> G.Defs.Collections.NtSet.t **)

  let ntsOfProd = function
  | (x, gamma) ->
    G.Defs.Collections.NtSet.add x (ntsOfGamma gamma)

  (** val ntsOf :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t **)

  let ntsOf g0 =
    fold_right (fun p acc ->
      G.Defs.Collections.NtSet.union (ntsOfProd p) acc)
      (G.Defs.Collections.NtSet.singleton (G.Defs.start g0))
      (G.Defs.prods g0)

  (** val lookaheadsOfGamma :
      G.Defs.symbol list -> G.Defs.Collections.LaSet.t **)

  let rec lookaheadsOfGamma = function
  | [] -> G.Defs.Collections.LaSet.empty
  | s :: gamma' ->
    (match s with
     | G.Defs.T y ->
       G.Defs.Collections.LaSet.add (G.Defs.Lookahead.LA y)
         (lookaheadsOfGamma gamma')
     | G.Defs.NT _ -> lookaheadsOfGamma gamma')

  (** val lookaheadsOf :
      G.Defs.grammar -> G.Defs.Collections.LaSet.t **)

  let lookaheadsOf g0 =
    fold_right (fun p acc ->
      let (_, gamma) = p in
      G.Defs.Collections.LaSet.union
        (lookaheadsOfGamma gamma) acc)
      (G.Defs.Collections.LaSet.singleton
        G.Defs.Lookahead.EOF) (G.Defs.prods g0)

  (** val numFollowCandidates :
      G.Defs.grammar -> G.Defs.Specs.follow_map -> nat **)

  let numFollowCandidates g0 fo =
    let allCandidates = product (ntsOf g0) (lookaheadsOf g0)
    in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fo))

  (** val mkFollowMap'_func :
      (G.Defs.grammar, (G.Defs.Collections.NtSet.t,
      (G.Defs.Specs.first_map, (__, (G.Defs.Specs.follow_map,
      __) sigT) sigT) sigT) sigT) sigT ->
      G.Defs.Specs.follow_map **)

  let rec mkFollowMap'_func x =
    let g0 = projT1 x in
    let nu = projT1 (projT2 x) in
    let fi = projT1 (projT2 (projT2 x)) in
    let fo = projT1 (projT2 (projT2 (projT2 (projT2 x)))) in
    let mkFollowMap'0 = fun g1 nu0 fi0 fo0 ->
      mkFollowMap'_func (ExistT (g1, (ExistT (nu0, (ExistT
        (fi0, (ExistT (__, (ExistT (fo0, __))))))))))
    in
    let fo' = followPass (G.Defs.prods g0) nu fi fo in
    if follow_map_equiv_dec fo fo'
    then fo
    else mkFollowMap'0 g0 nu fi fo'

  (** val mkFollowMap' :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
      G.Defs.Specs.follow_map **)

  let mkFollowMap' g0 nu fi fo =
    mkFollowMap'_func (ExistT (g0, (ExistT (nu, (ExistT (fi,
      (ExistT (__, (ExistT (fo, __))))))))))

  (** val initial_fo :
      G.Defs.grammar -> G.Defs.Collections.LaSet.t
      G.Defs.Collections.NtMap.t **)

  let initial_fo g0 =
    G.Defs.Collections.NtMap.add (G.Defs.start g0)
      (G.Defs.Collections.LaSet.singleton
        G.Defs.Lookahead.EOF) G.Defs.Collections.NtMap.empty

  (** val mkFollowMap :
      G.Defs.grammar -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Specs.follow_map **)

  let mkFollowMap g0 nu fi =
    mkFollowMap' g0 nu fi (initial_fo g0)

  type table_entry =
    (G.SymTy.nonterminal * G.Defs.Lookahead.lookahead) * G.Defs.symbol
    list

  (** val table_entry_dec :
      table_entry -> table_entry -> bool **)

  let table_entry_dec e e2 =
    let (x, x0) = e in
    let (p, l) = e2 in
    if let (x1, x2) = x in
       let (n, l0) = p in
       if G.SymTy.nt_eq_dec x1 n
       then G.Defs.Lookahead.lookahead_rect (fun t0 x3 ->
              match x3 with
              | G.Defs.Lookahead.LA t1 ->
                G.SymTy.t_eq_dec t0 t1
              | G.Defs.Lookahead.EOF -> false) (fun x3 ->
              match x3 with
              | G.Defs.Lookahead.LA _ -> false
              | G.Defs.Lookahead.EOF -> true) x2 l0
       else false
    then let rec f l0 x1 =
           match l0 with
           | [] ->
             (match x1 with
              | [] -> true
              | _ :: _ -> false)
           | y :: l1 ->
             (match x1 with
              | [] -> false
              | s :: l2 ->
                if G.Defs.symbol_rect (fun t0 x2 ->
                     match x2 with
                     | G.Defs.T t1 -> G.SymTy.t_eq_dec t0 t1
                     | G.Defs.NT _ -> false) (fun n x2 ->
                     match x2 with
                     | G.Defs.T _ -> false
                     | G.Defs.NT n0 -> G.SymTy.nt_eq_dec n n0)
                     y s
                then f l1 l2
                else false)
         in f x0 l
    else false

  (** val fromLookaheadList :
      G.SymTy.nonterminal -> G.Defs.symbol list ->
      G.Defs.Lookahead.lookahead list -> table_entry list **)

  let fromLookaheadList x gamma las =
    map (fun la -> ((x, la), gamma)) las

  (** val firstGamma' :
      G.Defs.symbol list -> G.Defs.Collections.NtSet.t ->
      G.Defs.Specs.first_map -> G.Defs.Lookahead.lookahead
      list **)

  let rec firstGamma' gamma nu fi =
    match gamma with
    | [] -> []
    | s :: gamma' ->
      (match s with
       | G.Defs.T y -> (G.Defs.Lookahead.LA y) :: []
       | G.Defs.NT x ->
         let xFirst =
           match G.Defs.Collections.NtMap.find x fi with
           | Some s0 -> G.Defs.Collections.LaSet.elements s0
           | None -> []
         in
         if G.Defs.Collections.NtSet.mem x nu
         then app xFirst (firstGamma' gamma' nu fi)
         else xFirst)

  (** val firstEntries :
      G.SymTy.nonterminal -> G.Defs.symbol list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      table_entry list **)

  let firstEntries x gamma nu fi =
    fromLookaheadList x gamma (firstGamma' gamma nu fi)

  (** val followLookahead :
      G.Defs.Collections.NtMap.key -> G.Defs.symbol list ->
      G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t
      -> G.Defs.Collections.LaSet.elt list **)

  let followLookahead x gamma nu fo =
    if nullableGamma gamma nu
    then (match G.Defs.Collections.NtMap.find x fo with
          | Some s -> G.Defs.Collections.LaSet.elements s
          | None -> [])
    else []

  (** val followEntries :
      G.SymTy.nonterminal -> G.Defs.symbol list ->
      G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t
      -> table_entry list **)

  let followEntries x gamma nu fo =
    fromLookaheadList x gamma (followLookahead x gamma nu fo)

  (** val entriesForProd :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t
      -> G.Defs.production -> table_entry list **)

  let entriesForProd nu fi fo = function
  | (x, gamma) ->
    app (firstEntries x gamma nu fi)
      (followEntries x gamma nu fo)

  (** val mkEntries' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t
      -> G.Defs.production list -> table_entry list **)

  let mkEntries' nu fi fo ps =
    flat_map (entriesForProd nu fi fo) ps

  (** val mkEntries :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t
      -> G.Defs.grammar -> table_entry list **)

  let mkEntries nu fi fo g0 =
    mkEntries' nu fi fo (G.Defs.prods g0)

  (** val empty_table :
      G.Defs.symbol list G.Defs.Collections.ParseTable.t **)

  let empty_table =
    G.Defs.Collections.ParseTable.empty

  (** val addEntry :
      table_entry -> G.Defs.Collections.parse_table option ->
      G.Defs.Collections.parse_table option **)

  let addEntry p = function
  | Some tbl ->
    let (p0, gamma) = p in
    let (x, la) = p0 in
    (match G.Defs.Utils.pt_lookup x la tbl with
     | Some gamma' ->
       if list_eq_dec G.Defs.symbol_eq_dec gamma gamma'
       then Some tbl
       else None
     | None -> Some (G.Defs.Utils.pt_add x la gamma tbl))
  | None -> None

  (** val mkParseTable :
      table_entry list -> G.Defs.Collections.parse_table
      option **)

  let mkParseTable ps =
    fold_right addEntry (Some empty_table) ps
 end

module NullableProofsFn =
 functor (G:T) ->
 struct
  module Gen = GeneratorFn(G)
 end

module FirstProofsFn =
 functor (G:T) ->
 struct
  module NullableProofs = NullableProofsFn(G)
 end

module FollowProofsFn =
 functor (G:T) ->
 struct
  module FirstProofs = FirstProofsFn(G)
 end

module EntryProofsFn =
 functor (G:T) ->
 struct
  module L = LemmasFn(G)

  module FollowProofs = FollowProofsFn(G)
 end

module GeneratorProofsFn =
 functor (G:T) ->
 struct
  module EntryProofs = EntryProofsFn(G)
 end

module ParserSoundnessFn =
 functor (G:T) ->
 struct
  module ParserDefs = ParserFn(G)

  module L = LemmasFn(G)
 end

module ParserSafetyFn =
 functor (G:T) ->
 struct
  module ParserSoundness = ParserSoundnessFn(G)

  module L = LemmasFn(G)

  (** val nullTree : G.Defs.Tree.tree -> bool **)

  let rec nullTree = function
  | G.Defs.Tree.Leaf _ -> false
  | G.Defs.Tree.Node (_, sts) ->
    let rec nullForest0 = function
    | [] -> true
    | t0 :: l' -> (&&) (nullTree t0) (nullForest0 l')
    in nullForest0 sts

  (** val nullForest : G.Defs.Tree.tree list -> bool **)

  let rec nullForest = function
  | [] -> true
  | t0 :: l' -> (&&) (nullTree t0) (nullForest l')

  (** val reachableNts :
      G.Defs.Tree.tree -> G.Defs.Collections.NtSet.t **)

  let rec reachableNts = function
  | G.Defs.Tree.Leaf _ -> G.Defs.Collections.NtSet.empty
  | G.Defs.Tree.Node (x, sts) ->
    let reachableNtsF0 =
      let rec reachableNtsF0 = function
      | [] -> G.Defs.Collections.NtSet.empty
      | t0 :: l' ->
        if nullTree t0
        then G.Defs.Collections.NtSet.union (reachableNts t0)
               (reachableNtsF0 l')
        else reachableNts t0
      in reachableNtsF0
    in
    G.Defs.Collections.NtSet.add x (reachableNtsF0 sts)

  (** val reachableNtsF :
      G.Defs.Tree.tree list -> G.Defs.Collections.NtSet.t **)

  let rec reachableNtsF = function
  | [] -> G.Defs.Collections.NtSet.empty
  | t0 :: l' ->
    if nullTree t0
    then G.Defs.Collections.NtSet.union (reachableNts t0)
           (reachableNtsF l')
    else reachableNts t0

  (** val parse_wrapper :
      G.Defs.Collections.parse_table -> G.Defs.symbol ->
      G.SymTy.terminal list ->
      (ParserSoundness.ParserDefs.parse_failure,
      G.Defs.Tree.tree * (G.SymTy.terminal list,
      G.SymTy.terminal
      ParserSoundness.ParserDefs.length_lt_eq) sigT) sum **)

  let parse_wrapper tbl sym input =
    ParserSoundness.ParserDefs.parseTree tbl sym input
      G.Defs.Collections.NtSet.empty

  (** val sa_size :
      ParserSoundness.ParserDefs.sym_arg -> nat **)

  let sa_size = function
  | ParserSoundness.ParserDefs.F_arg _ -> O
  | ParserSoundness.ParserDefs.G_arg gamma ->
    add (S O) (length gamma)
 end

module ParserProofsFn =
 functor (G:T) ->
 struct
  module ParserSafety = ParserSafetyFn(G)

  module L = LemmasFn(G)
 end

module Main =
 functor (G:T) ->
 struct
  module GeneratorAndProofs = GeneratorProofsFn(G)

  module ParserAndProofs = ParserProofsFn(G)

  (** val parseTableOf :
      G.Defs.grammar -> G.Defs.Collections.parse_table option **)

  let parseTableOf g0 =
    let nu =
      GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkNullableSet
        g0
    in
    let fi =
      GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkFirstMap
        g0 nu
    in
    let fo =
      GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkFollowMap
        g0 nu fi
    in
    let es =
      GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkEntries
        nu fi fo g0
    in
    GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkParseTable
      es

  (** val parse :
      G.Defs.Collections.parse_table -> G.Defs.symbol ->
      G.SymTy.terminal list ->
      (ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parse_failure,
      G.Defs.Tree.tree * G.SymTy.terminal list) sum **)

  let parse tbl sym input =
    match ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parseTree
            tbl sym input G.Defs.Collections.NtSet.empty with
    | Inl failure -> Inl failure
    | Inr p ->
      let (tr, s) = p in
      let ExistT (input', _) = s in Inr (tr, input')
 end

module NatStringTypes =
 struct
  type terminal = char list

  type nonterminal = nat

  type literal = char list

  (** val t_eq_dec : char list -> char list -> bool **)

  let t_eq_dec =
    string_dec

  (** val nt_eq_dec : nat -> nat -> bool **)

  let nt_eq_dec =
    Nat.eq_dec
 end

module NatStringGrammar =
 struct
  module SymTy = NatStringTypes

  module Defs = DefsFn(SymTy)
 end

(** val value : nat **)

let value =
  O

(** val pairs : nat **)

let pairs =
  S O

(** val pairs' : nat **)

let pairs' =
  S (S O)

(** val pair : nat **)

let pair =
  S (S (S O))

(** val elts : nat **)

let elts =
  S (S (S (S O)))

(** val elts' : nat **)

let elts' =
  S (S (S (S (S O))))

(** val g : NatStringGrammar.Defs.grammar **)

let g =
  { NatStringGrammar.Defs.start = value;
    NatStringGrammar.Defs.prods = ((value,
    ((NatStringGrammar.Defs.T
    ('{'::[])) :: ((NatStringGrammar.Defs.NT
    pairs) :: ((NatStringGrammar.Defs.T
    ('}'::[])) :: [])))) :: ((value,
    ((NatStringGrammar.Defs.T
    ('['::[])) :: ((NatStringGrammar.Defs.NT
    elts) :: ((NatStringGrammar.Defs.T
    (']'::[])) :: [])))) :: ((value,
    ((NatStringGrammar.Defs.T
    ('S'::('T'::('R'::('I'::('N'::('G'::[]))))))) :: [])) :: ((value,
    ((NatStringGrammar.Defs.T
    ('I'::('N'::('T'::[])))) :: [])) :: ((value,
    ((NatStringGrammar.Defs.T
    ('F'::('L'::('O'::('A'::('T'::[])))))) :: [])) :: ((value,
    ((NatStringGrammar.Defs.T
    ('T'::('R'::('U'::('E'::[]))))) :: [])) :: ((value,
    ((NatStringGrammar.Defs.T
    ('F'::('A'::('L'::('S'::('E'::[])))))) :: [])) :: ((value,
    ((NatStringGrammar.Defs.T
    ('N'::('U'::('L'::('L'::[]))))) :: [])) :: ((pairs,
    []) :: ((pairs, ((NatStringGrammar.Defs.NT
    pair) :: ((NatStringGrammar.Defs.NT
    pairs') :: []))) :: ((pairs', []) :: ((pairs',
    ((NatStringGrammar.Defs.T
    (','::[])) :: ((NatStringGrammar.Defs.NT
    pair) :: ((NatStringGrammar.Defs.NT
    pairs') :: [])))) :: ((pair, ((NatStringGrammar.Defs.T
    ('S'::('T'::('R'::('I'::('N'::('G'::[]))))))) :: ((NatStringGrammar.Defs.T
    (':'::[])) :: ((NatStringGrammar.Defs.NT
    value) :: [])))) :: ((elts, []) :: ((elts,
    ((NatStringGrammar.Defs.NT
    value) :: ((NatStringGrammar.Defs.NT
    elts') :: []))) :: ((elts', []) :: ((elts',
    ((NatStringGrammar.Defs.T
    (','::[])) :: ((NatStringGrammar.Defs.NT
    value) :: ((NatStringGrammar.Defs.NT
    elts') :: [])))) :: []))))))))))))))))) }

module PG = Main(NatStringGrammar)
