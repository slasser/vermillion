
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

(** val in_dec :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool **)

let rec in_dec h a = function
| [] -> false
| y :: l0 ->
  let s = h y a in if s then true else in_dec h a l0

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

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

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

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

  let fold_rel f g i j s rempty rstep =
    let l = rev (M.elements s) in
    let rstep' = fun x a b x0 -> rstep x a b __ x0 in
    let rec f0 l0 rstep'0 =
      match l0 with
      | [] -> rempty
      | y :: l1 ->
        rstep'0 y (fold_right f i l1) (fold_right g j l1) __
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

(** val prependToAll :
    char list -> char list list -> char list **)

let rec prependToAll sep = function
| [] -> []
| s :: ss' -> append sep (append s (prependToAll sep ss'))

(** val intersperse :
    char list -> char list list -> char list **)

let intersperse sep = function
| [] -> []
| s :: ss' -> append s (prependToAll sep ss')

type tuple = __

module type SYMBOL_TYPES =
 sig
  type terminal

  type nonterminal

  val t_eq_dec : terminal -> terminal -> bool

  val nt_eq_dec : nonterminal -> nonterminal -> bool

  val showT : terminal -> char list

  val showNT : nonterminal -> char list

  type t_semty

  type nt_semty
 end

module DefsFn =
 functor (Ty:SYMBOL_TYPES) ->
 struct
  module CoreDefs =
   struct
    type symbol =
    | T of Ty.terminal
    | NT of Ty.nonterminal

    (** val symbol_rect :
        (Ty.terminal -> 'a1) -> (Ty.nonterminal -> 'a1) ->
        symbol -> 'a1 **)

    let symbol_rect f f0 = function
    | T x -> f x
    | NT x -> f0 x

    (** val symbol_rec :
        (Ty.terminal -> 'a1) -> (Ty.nonterminal -> 'a1) ->
        symbol -> 'a1 **)

    let symbol_rec f f0 = function
    | T x -> f x
    | NT x -> f0 x

    (** val symbol_eq_dec : symbol -> symbol -> bool **)

    let symbol_eq_dec s s' =
      match s with
      | T x ->
        (match s' with
         | T t0 -> Ty.t_eq_dec x t0
         | NT _ -> false)
      | NT x ->
        (match s' with
         | T _ -> false
         | NT n0 -> Ty.nt_eq_dec x n0)

    type symbol_semty = __

    type rhs_semty = tuple

    type base_production = Ty.nonterminal * symbol list

    type action_ty = __

    type production = (base_production, action_ty) sigT

    type token = (Ty.terminal, Ty.t_semty) sigT

    type grammar = { start : Ty.nonterminal;
                     prods : production list }

    (** val start : grammar -> Ty.nonterminal **)

    let start g =
      g.start

    (** val prods : grammar -> production list **)

    let prods g =
      g.prods
   end

  module Tree =
   struct
    type tree =
    | Leaf of Ty.terminal
    | Node of Ty.nonterminal * tree list

    (** val tree_rect :
        (Ty.terminal -> 'a1) -> (Ty.nonterminal -> tree list
        -> 'a1) -> tree -> 'a1 **)

    let tree_rect f f0 = function
    | Leaf x -> f x
    | Node (x, x0) -> f0 x x0

    (** val tree_rec :
        (Ty.terminal -> 'a1) -> (Ty.nonterminal -> tree list
        -> 'a1) -> tree -> 'a1 **)

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
    | LA of Ty.terminal
    | EOF

    (** val lookahead_rect :
        (Ty.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1 **)

    let lookahead_rect f f0 = function
    | LA x -> f x
    | EOF -> f0

    (** val lookahead_rec :
        (Ty.terminal -> 'a1) -> 'a1 -> lookahead -> 'a1 **)

    let lookahead_rec f f0 = function
    | LA x -> f x
    | EOF -> f0

    (** val showLookahead : lookahead -> char list **)

    let showLookahead = function
    | LA a -> Ty.showT a
    | EOF -> 'E'::('O'::('F'::[]))
   end

  module Collections =
   struct
    module MDT_NT =
     struct
      type t = Ty.nonterminal

      (** val eq_dec :
          Ty.nonterminal -> Ty.nonterminal -> bool **)

      let eq_dec =
        Ty.nt_eq_dec
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
         | Lookahead.LA t0 -> Ty.t_eq_dec x t0
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

    type pt_key = Ty.nonterminal * Lookahead.lookahead

    (** val pt_key_eq_dec : pt_key -> pt_key -> bool **)

    let pt_key_eq_dec k k2 =
      let (x, x0) = k in
      let (n, l) = k2 in
      if Ty.nt_eq_dec x n
      then (match x0 with
            | Lookahead.LA x1 ->
              (match l with
               | Lookahead.LA t0 -> Ty.t_eq_dec x1 t0
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

    type parse_table = CoreDefs.production ParseTable.t
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
        CoreDefs.token list -> Lookahead.lookahead **)

    let peek = function
    | [] -> Lookahead.EOF
    | t0 :: _ -> let ExistT (a, _) = t0 in Lookahead.LA a
   end

  module Utils =
   struct
    (** val isNT : CoreDefs.symbol -> bool **)

    let isNT = function
    | CoreDefs.T _ -> false
    | CoreDefs.NT _ -> true

    (** val isT : CoreDefs.symbol -> bool **)

    let isT = function
    | CoreDefs.T _ -> true
    | CoreDefs.NT _ -> false

    (** val lhs : CoreDefs.production -> Ty.nonterminal **)

    let lhs = function
    | ExistT (x0, _) -> let (x, _) = x0 in x

    (** val rhs :
        CoreDefs.production -> CoreDefs.symbol list **)

    let rhs = function
    | ExistT (x, _) -> let (_, gamma) = x in gamma

    (** val baseProduction :
        CoreDefs.production -> CoreDefs.base_production **)

    let baseProduction = function
    | ExistT (b, _) -> b

    (** val baseProductions :
        CoreDefs.grammar -> CoreDefs.base_production list **)

    let baseProductions g =
      map baseProduction (CoreDefs.prods g)

    (** val pt_lookup :
        Ty.nonterminal -> Lookahead.lookahead ->
        Collections.parse_table -> CoreDefs.production option **)

    let pt_lookup x la tbl =
      Collections.ParseTable.find (x, la) tbl

    (** val pt_add :
        Ty.nonterminal -> Lookahead.lookahead ->
        CoreDefs.production -> Collections.parse_table ->
        Collections.parse_table **)

    let pt_add x la p tbl =
      Collections.ParseTable.add (x, la) p tbl

    (** val fromNtList :
        Ty.nonterminal list -> Collections.NtSet.t **)

    let fromNtList ls =
      fold_right Collections.NtSet.add
        Collections.NtSet.empty ls
   end

  module Formatting =
   struct
    (** val showSymbol : CoreDefs.symbol -> char list **)

    let showSymbol = function
    | CoreDefs.T a -> append ('T'::(' '::[])) (Ty.showT a)
    | CoreDefs.NT x ->
      append ('N'::('T'::(' '::[]))) (Ty.showNT x)

    (** val showRhs : CoreDefs.symbol list -> char list **)

    let showRhs gamma =
      intersperse (','::(' '::[])) (map showSymbol gamma)

    (** val showBaseProd :
        CoreDefs.base_production -> char list **)

    let showBaseProd = function
    | (x, gamma) ->
      append (Ty.showNT x)
        (append (' '::('-'::('-'::('>'::(' '::[])))))
          (showRhs gamma))

    (** val showProd : CoreDefs.production -> char list **)

    let showProd p =
      showBaseProd (Utils.baseProduction p)
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
    module CoreDefs :
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

      type symbol_semty = __

      type rhs_semty = tuple

      type base_production = SymTy.nonterminal * symbol list

      type action_ty = __

      type production = (base_production, action_ty) sigT

      type token = (SymTy.terminal, SymTy.t_semty) sigT

      type grammar = { start : SymTy.nonterminal;
                       prods : production list }

      val start : grammar -> SymTy.nonterminal

      val prods : grammar -> production list
     end

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

      val showLookahead : lookahead -> char list
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

      type parse_table = CoreDefs.production ParseTable.t
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
      val peek : CoreDefs.token list -> Lookahead.lookahead
     end

    module Utils :
     sig
      val isNT : CoreDefs.symbol -> bool

      val isT : CoreDefs.symbol -> bool

      val lhs : CoreDefs.production -> SymTy.nonterminal

      val rhs : CoreDefs.production -> CoreDefs.symbol list

      val baseProduction :
        CoreDefs.production -> CoreDefs.base_production

      val baseProductions :
        CoreDefs.grammar -> CoreDefs.base_production list

      val pt_lookup :
        SymTy.nonterminal -> Lookahead.lookahead ->
        Collections.parse_table -> CoreDefs.production option

      val pt_add :
        SymTy.nonterminal -> Lookahead.lookahead ->
        CoreDefs.production -> Collections.parse_table ->
        Collections.parse_table

      val fromNtList :
        SymTy.nonterminal list -> Collections.NtSet.t
     end

    module Formatting :
     sig
      val showSymbol : CoreDefs.symbol -> char list

      val showRhs : CoreDefs.symbol list -> char list

      val showBaseProd : CoreDefs.base_production -> char list

      val showProd : CoreDefs.production -> char list
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
  (** val base_production_eq_dec :
      G.Defs.CoreDefs.base_production ->
      G.Defs.CoreDefs.base_production -> bool **)

  let base_production_eq_dec b b' =
    let (x, x0) = b in
    let (n, l) = b' in
    if G.SymTy.nt_eq_dec x n
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
                if G.Defs.CoreDefs.symbol_rect (fun t0 x2 ->
                     match x2 with
                     | G.Defs.CoreDefs.T t1 ->
                       G.SymTy.t_eq_dec t0 t1
                     | G.Defs.CoreDefs.NT _ -> false)
                     (fun n0 x2 ->
                     match x2 with
                     | G.Defs.CoreDefs.T _ -> false
                     | G.Defs.CoreDefs.NT n1 ->
                       G.SymTy.nt_eq_dec n0 n1) y s
                then f l1 l2
                else false)
         in f x0 l
    else false
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
  | F_arg of G.Defs.CoreDefs.symbol
  | G_arg of G.Defs.CoreDefs.symbol list

  (** val sym_arg_rect :
      (G.Defs.CoreDefs.symbol -> 'a1) ->
      (G.Defs.CoreDefs.symbol list -> 'a1) -> sym_arg -> 'a1 **)

  let sym_arg_rect f f0 = function
  | F_arg x -> f x
  | G_arg x -> f0 x

  (** val sym_arg_rec :
      (G.Defs.CoreDefs.symbol -> 'a1) ->
      (G.Defs.CoreDefs.symbol list -> 'a1) -> sym_arg -> 'a1 **)

  let sym_arg_rec f f0 = function
  | F_arg x -> f x
  | G_arg x -> f0 x

  (** val sa_size : sym_arg -> nat **)

  let sa_size = function
  | F_arg _ -> O
  | G_arg gamma -> add (S O) (length gamma)

  (** val nt_keys :
      G.Defs.Collections.parse_table -> G.SymTy.nonterminal
      list **)

  let nt_keys tbl =
    map (fun pr -> let (y, _) = pr in let (x, _) = y in x)
      (G.Defs.Collections.ParseTable.elements tbl)

  (** val ptlk_dec :
      G.SymTy.nonterminal -> G.Defs.Lookahead.lookahead ->
      G.Defs.Collections.parse_table -> (__,
      G.Defs.CoreDefs.production) sum **)

  let ptlk_dec x la tbl =
    let o = G.Defs.Utils.pt_lookup x la tbl in
    (match o with
     | Some p -> Inr p
     | None -> Inl __)

  (** val meas :
      G.Defs.Collections.parse_table -> G.Defs.CoreDefs.token
      list -> G.Defs.Collections.NtSet.t -> sym_arg ->
      (nat * nat) * nat **)

  let meas tbl tokens vis sa =
    (((length tokens),
      (G.Defs.Collections.NtSet.cardinal
        (G.Defs.Collections.NtSet.diff
          (G.Defs.Utils.fromNtList (nt_keys tbl)) vis))),
      (sa_size sa))

  type parse_failure =
  | Reject of char list * G.Defs.CoreDefs.token list
  | Error of char list * G.SymTy.nonterminal
     * G.Defs.CoreDefs.token list

  (** val parse_failure_rect :
      (char list -> G.Defs.CoreDefs.token list -> 'a1) ->
      (char list -> G.SymTy.nonterminal ->
      G.Defs.CoreDefs.token list -> 'a1) -> parse_failure ->
      'a1 **)

  let parse_failure_rect f f0 = function
  | Reject (x, x0) -> f x x0
  | Error (x, x0, x1) -> f0 x x0 x1

  (** val parse_failure_rec :
      (char list -> G.Defs.CoreDefs.token list -> 'a1) ->
      (char list -> G.SymTy.nonterminal ->
      G.Defs.CoreDefs.token list -> 'a1) -> parse_failure ->
      'a1 **)

  let parse_failure_rec f f0 = function
  | Reject (x, x0) -> f x x0
  | Error (x, x0, x1) -> f0 x x0 x1

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

  (** val mismatchMessage :
      G.SymTy.terminal -> G.SymTy.terminal -> char list **)

  let mismatchMessage a a' =
    append
      ('T'::('o'::('k'::('e'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::(';'::(' '::('e'::('x'::('p'::('e'::('c'::('t'::('e'::('d'::(' '::[])))))))))))))))))))))))))
      (append (G.SymTy.showT a)
        (append (','::(' '::('s'::('a'::('w'::(' '::[]))))))
          (G.SymTy.showT a')))

  (** val parseSymbol :
      G.Defs.Collections.parse_table ->
      G.Defs.CoreDefs.symbol -> G.Defs.CoreDefs.token list ->
      G.Defs.Collections.NtSet.t -> (parse_failure,
      G.Defs.CoreDefs.symbol_semty * (G.Defs.CoreDefs.token
      list, G.Defs.CoreDefs.token length_lt_eq) sigT) sum **)

  let rec parseSymbol tbl sym ts vis =
    match sym with
    | G.Defs.CoreDefs.T a ->
      (match ts with
       | [] ->
         Inl (Reject
           (('i'::('n'::('p'::('u'::('t'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::[]))))))))))))))),
           ts))
       | t0 :: ts' ->
         let ExistT (a', v') = t0 in
         if t_eq_dec a' a
         then Inr ((Obj.magic v'), (ExistT (ts',
                (length_lt_eq_cons ts (ExistT (a', v')) ts'))))
         else Inl (Reject ((mismatchMessage a a'), ts)))
    | G.Defs.CoreDefs.NT x ->
      if mem_dec x vis
      then Inl (Error
             (('l'::('e'::('f'::('t'::(' '::('r'::('e'::('c'::('u'::('r'::('s'::('i'::('o'::('n'::(' '::('d'::('e'::('t'::('e'::('c'::('t'::('e'::('d'::[]))))))))))))))))))))))),
             x, ts))
      else (match ptlk_dec x (G.Defs.Derivation.peek ts) tbl with
            | Inl _ ->
              Inl (Reject
                (('l'::('o'::('o'::('k'::('u'::('p'::(' '::('f'::('a'::('i'::('l'::('u'::('r'::('e'::[])))))))))))))),
                ts))
            | Inr s ->
              let ExistT (x0, f) = s in
              let (x', gamma) = x0 in
              if nt_eq_dec x' x
              then (match parseGamma tbl gamma ts
                            (G.Defs.Collections.NtSet.add x
                              vis) with
                    | Inl pfail -> Inl pfail
                    | Inr p ->
                      let (vs, s0) = p in
                      let v = Obj.magic f vs in Inr (v, s0))
              else Inl (Error
                     (('m'::('a'::('l'::('f'::('o'::('r'::('m'::('e'::('d'::(' '::('p'::('a'::('r'::('s'::('e'::(' '::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
                     x, ts)))

  (** val parseGamma :
      G.Defs.Collections.parse_table ->
      G.Defs.CoreDefs.symbol list -> G.Defs.CoreDefs.token
      list -> G.Defs.Collections.NtSet.t -> (parse_failure,
      G.Defs.CoreDefs.rhs_semty * (G.Defs.CoreDefs.token
      list, G.Defs.CoreDefs.token length_lt_eq) sigT) sum **)

  and parseGamma tbl gamma ts vis =
    match gamma with
    | [] ->
      let vs = () in
      Inr ((Obj.magic vs), (ExistT (ts,
      (length_lt_eq_refl ts))))
    | sym :: gamma' ->
      (match parseSymbol tbl sym ts vis with
       | Inl pfail -> Inl pfail
       | Inr p ->
         let (lSib, s) = p in
         let ExistT (ts', hle) = s in
         if hle
         then (match parseGamma tbl gamma' ts'
                       G.Defs.Collections.NtSet.empty with
               | Inl pfail -> Inl pfail
               | Inr p0 ->
                 let (rSibs, s0) = p0 in
                 let ExistT (ts'', hle'') = s0 in
                 let vs = (lSib, rSibs) in
                 Inr ((Obj.magic vs), (ExistT (ts'',
                 (length_lt_eq_trans ts'' ts' ts hle'' hle)))))
         else (match parseGamma tbl gamma' ts vis with
               | Inl pfail -> Inl pfail
               | Inr p0 ->
                 let (rSibs, s0) = p0 in
                 let vs = (lSib, rSibs) in
                 Inr ((Obj.magic vs), s0)))
 end

(** val findDup :
    ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec findDup eq_dec0 = function
| [] -> None
| x :: l' ->
  if in_dec eq_dec0 x l' then Some x else findDup eq_dec0 l'

module GeneratorFn =
 functor (G:T) ->
 struct
  module L = LemmasFn(G)

  (** val lhSet :
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t **)

  let lhSet ps =
    G.Defs.Utils.fromNtList (map G.Defs.Utils.lhs ps)

  (** val nullableGamma :
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.NtSet.t -> bool **)

  let rec nullableGamma gamma nu =
    match gamma with
    | [] -> true
    | s :: gamma' ->
      (match s with
       | G.Defs.CoreDefs.T _ -> false
       | G.Defs.CoreDefs.NT x ->
         if G.Defs.Collections.NtSet.mem x nu
         then nullableGamma gamma' nu
         else false)

  (** val updateNu :
      G.Defs.CoreDefs.production ->
      G.Defs.Collections.NtSet.t -> G.Defs.Collections.NtSet.t **)

  let updateNu p nu =
    let ExistT (x0, _) = p in
    let (x, gamma) = x0 in
    if nullableGamma gamma nu
    then G.Defs.Collections.NtSet.add x nu
    else nu

  (** val nullablePass :
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Collections.NtSet.t **)

  let nullablePass ps nu =
    fold_right updateNu nu ps

  (** val countNullCands :
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t -> nat **)

  let countNullCands ps nu =
    let candidates = lhSet ps in
    G.Defs.Collections.NtSet.cardinal
      (G.Defs.Collections.NtSet.diff candidates nu)

  (** val mkNullableSet'_func :
      (G.Defs.CoreDefs.production list,
      G.Defs.Collections.NtSet.t) sigT ->
      G.Defs.Collections.NtSet.t **)

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
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Collections.NtSet.t **)

  let mkNullableSet' ps nu =
    mkNullableSet'_func (ExistT (ps, nu))

  (** val mkNullableSet :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.NtSet.t **)

  let mkNullableSet g =
    mkNullableSet' (G.Defs.CoreDefs.prods g)
      G.Defs.Collections.NtSet.empty

  (** val nullableSym :
      G.Defs.CoreDefs.symbol -> G.Defs.Collections.NtSet.t ->
      bool **)

  let nullableSym sym nu =
    match sym with
    | G.Defs.CoreDefs.T _ -> false
    | G.Defs.CoreDefs.NT x ->
      G.Defs.Collections.NtSet.mem x nu

  (** val findOrEmpty :
      G.SymTy.nonterminal -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t **)

  let findOrEmpty x fi =
    match G.Defs.Collections.NtMap.find x fi with
    | Some s -> s
    | None -> G.Defs.Collections.LaSet.empty

  (** val firstSym :
      G.Defs.CoreDefs.symbol -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t **)

  let firstSym sym fi =
    match sym with
    | G.Defs.CoreDefs.T y ->
      G.Defs.Collections.LaSet.singleton (G.Defs.Lookahead.LA
        y)
    | G.Defs.CoreDefs.NT x -> findOrEmpty x fi

  (** val firstGamma :
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Collections.LaSet.t **)

  let rec firstGamma gamma nu fi =
    match gamma with
    | [] -> G.Defs.Collections.LaSet.empty
    | sym :: gamma' ->
      if nullableSym sym nu
      then G.Defs.Collections.LaSet.union (firstSym sym fi)
             (firstGamma gamma' nu fi)
      else firstSym sym fi

  (** val updateFi :
      G.Defs.Collections.NtSet.t ->
      G.Defs.CoreDefs.production -> G.Defs.Specs.first_map ->
      G.Defs.Specs.first_map **)

  let updateFi nu p fi =
    let ExistT (x0, _) = p in
    let (x, gamma) = x0 in
    let fg = firstGamma gamma nu fi in
    let xFirst = findOrEmpty x fi in
    let xFirst' = G.Defs.Collections.LaSet.union fg xFirst in
    if G.Defs.Collections.LaSet.eq_dec xFirst xFirst'
    then fi
    else G.Defs.Collections.NtMap.add x xFirst' fi

  (** val firstPass :
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.first_map **)

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
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Lookahead.lookahead option **)

  let rec leftmostLookahead = function
  | [] -> None
  | s :: gamma' ->
    (match s with
     | G.Defs.CoreDefs.T y -> Some (G.Defs.Lookahead.LA y)
     | G.Defs.CoreDefs.NT _ -> leftmostLookahead gamma')

  (** val leftmostLookaheads' :
      G.Defs.CoreDefs.symbol list list ->
      G.Defs.Collections.LaSet.t **)

  let leftmostLookaheads' gammas =
    fold_right (fun gamma acc ->
      match leftmostLookahead gamma with
      | Some la -> G.Defs.Collections.LaSet.add la acc
      | None -> acc) G.Defs.Collections.LaSet.empty gammas

  (** val leftmostLookaheads :
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.LaSet.t **)

  let leftmostLookaheads ps =
    leftmostLookaheads' (map G.Defs.Utils.rhs ps)

  (** val product :
      G.Defs.Collections.NtSet.t ->
      G.Defs.Collections.LaSet.t -> PairSet.t **)

  let product n l =
    let f = fun x acc -> PairSet.union (mkPairs x l) acc in
    G.Defs.Collections.NtSet.fold f n PairSet.empty

  (** val countFirstCands :
      G.Defs.CoreDefs.production list ->
      G.Defs.Specs.first_map -> nat **)

  let countFirstCands ps fi =
    let allCandidates =
      product (lhSet ps) (leftmostLookaheads ps)
    in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fi))

  (** val mkFirstMap'_func :
      (G.Defs.CoreDefs.production list,
      (G.Defs.Collections.NtSet.t, (G.Defs.Specs.first_map,
      __) sigT) sigT) sigT -> G.Defs.Specs.first_map **)

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
      G.Defs.CoreDefs.production list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.first_map **)

  let mkFirstMap' ps nu fi =
    mkFirstMap'_func (ExistT (ps, (ExistT (nu, (ExistT (fi,
      __))))))

  (** val empty_fi :
      G.Defs.Collections.LaSet.t G.Defs.Collections.NtMap.t **)

  let empty_fi =
    G.Defs.Collections.NtMap.empty

  (** val mkFirstMap :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.NtSet.t
      -> G.Defs.Specs.first_map **)

  let mkFirstMap g nu =
    mkFirstMap' (G.Defs.CoreDefs.prods g) nu empty_fi

  (** val updateFo' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.SymTy.nonterminal -> G.Defs.CoreDefs.symbol list ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map **)

  let rec updateFo' nu fi lx gamma fo =
    match gamma with
    | [] -> fo
    | s :: gamma' ->
      (match s with
       | G.Defs.CoreDefs.T _ -> updateFo' nu fi lx gamma' fo
       | G.Defs.CoreDefs.NT rx ->
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
      G.Defs.CoreDefs.base_production ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map **)

  let updateFo nu fi b fo =
    let (x, gamma) = b in updateFo' nu fi x gamma fo

  (** val followPass :
      G.Defs.CoreDefs.base_production list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.Specs.follow_map **)

  let followPass ps nu fi fo =
    fold_right (updateFo nu fi) fo ps

  (** val follow_map_equiv_dec :
      G.Defs.Specs.first_map -> G.Defs.Specs.first_map -> bool **)

  let follow_map_equiv_dec =
    first_map_equiv_dec

  (** val ntsOfGamma :
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.NtSet.t **)

  let rec ntsOfGamma = function
  | [] -> G.Defs.Collections.NtSet.empty
  | s :: gamma' ->
    (match s with
     | G.Defs.CoreDefs.T _ -> ntsOfGamma gamma'
     | G.Defs.CoreDefs.NT x ->
       G.Defs.Collections.NtSet.add x (ntsOfGamma gamma'))

  (** val ntsOfProd :
      G.Defs.CoreDefs.base_production ->
      G.Defs.Collections.NtSet.t **)

  let ntsOfProd = function
  | (x, gamma) ->
    G.Defs.Collections.NtSet.add x (ntsOfGamma gamma)

  (** val ntsOf :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.NtSet.t **)

  let ntsOf g =
    fold_right (fun p acc ->
      G.Defs.Collections.NtSet.union (ntsOfProd p) acc)
      (G.Defs.Collections.NtSet.singleton
        (G.Defs.CoreDefs.start g))
      (G.Defs.Utils.baseProductions g)

  (** val lookaheadsOfGamma :
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.LaSet.t **)

  let rec lookaheadsOfGamma = function
  | [] -> G.Defs.Collections.LaSet.empty
  | s :: gamma' ->
    (match s with
     | G.Defs.CoreDefs.T y ->
       G.Defs.Collections.LaSet.add (G.Defs.Lookahead.LA y)
         (lookaheadsOfGamma gamma')
     | G.Defs.CoreDefs.NT _ -> lookaheadsOfGamma gamma')

  (** val lookaheadsOf :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.LaSet.t **)

  let lookaheadsOf g =
    fold_right (fun p acc ->
      let (_, gamma) = p in
      G.Defs.Collections.LaSet.union
        (lookaheadsOfGamma gamma) acc)
      (G.Defs.Collections.LaSet.singleton
        G.Defs.Lookahead.EOF) (G.Defs.Utils.baseProductions g)

  (** val countFollowCands :
      G.Defs.CoreDefs.grammar -> G.Defs.Specs.follow_map ->
      nat **)

  let countFollowCands g fo =
    let allCandidates = product (ntsOf g) (lookaheadsOf g) in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fo))

  (** val mkFollowMap'_func :
      (G.Defs.CoreDefs.grammar, (G.Defs.Collections.NtSet.t,
      (G.Defs.Specs.first_map, (__, (G.Defs.Specs.follow_map,
      __) sigT) sigT) sigT) sigT) sigT ->
      G.Defs.Specs.follow_map **)

  let rec mkFollowMap'_func x =
    let g = projT1 x in
    let nu = projT1 (projT2 x) in
    let fi = projT1 (projT2 (projT2 x)) in
    let fo = projT1 (projT2 (projT2 (projT2 (projT2 x)))) in
    let mkFollowMap'0 = fun g0 nu0 fi0 fo0 ->
      mkFollowMap'_func (ExistT (g0, (ExistT (nu0, (ExistT
        (fi0, (ExistT (__, (ExistT (fo0, __))))))))))
    in
    let fo' =
      followPass (G.Defs.Utils.baseProductions g) nu fi fo
    in
    if follow_map_equiv_dec fo fo'
    then fo
    else mkFollowMap'0 g nu fi fo'

  (** val mkFollowMap' :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.NtSet.t
      -> G.Defs.Specs.first_map -> G.Defs.Specs.follow_map ->
      G.Defs.Specs.follow_map **)

  let mkFollowMap' g nu fi fo =
    mkFollowMap'_func (ExistT (g, (ExistT (nu, (ExistT (fi,
      (ExistT (__, (ExistT (fo, __))))))))))

  (** val initial_fo :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.LaSet.t
      G.Defs.Collections.NtMap.t **)

  let initial_fo g =
    G.Defs.Collections.NtMap.add (G.Defs.CoreDefs.start g)
      (G.Defs.Collections.LaSet.singleton
        G.Defs.Lookahead.EOF) G.Defs.Collections.NtMap.empty

  (** val mkFollowMap :
      G.Defs.CoreDefs.grammar -> G.Defs.Collections.NtSet.t
      -> G.Defs.Specs.first_map -> G.Defs.Specs.follow_map **)

  let mkFollowMap g nu fi =
    mkFollowMap' g nu fi (initial_fo g)

  type table_entry =
    G.Defs.CoreDefs.production * G.Defs.Lookahead.lookahead

  (** val fromLookaheadList :
      G.Defs.CoreDefs.production ->
      G.Defs.Lookahead.lookahead list -> table_entry list **)

  let fromLookaheadList xp las =
    map (fun la -> (xp, la)) las

  (** val firstGamma' :
      G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Lookahead.lookahead list **)

  let rec firstGamma' gamma nu fi =
    match gamma with
    | [] -> []
    | s :: gamma' ->
      (match s with
       | G.Defs.CoreDefs.T y -> (G.Defs.Lookahead.LA y) :: []
       | G.Defs.CoreDefs.NT x ->
         let xFirst =
           match G.Defs.Collections.NtMap.find x fi with
           | Some s0 -> G.Defs.Collections.LaSet.elements s0
           | None -> []
         in
         if G.Defs.Collections.NtSet.mem x nu
         then app xFirst (firstGamma' gamma' nu fi)
         else xFirst)

  (** val firstEntries :
      G.Defs.CoreDefs.production ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      table_entry list **)

  let firstEntries xp nu fi =
    fromLookaheadList xp
      (firstGamma' (G.Defs.Utils.rhs xp) nu fi)

  (** val followLookahead :
      G.SymTy.nonterminal -> G.Defs.CoreDefs.symbol list ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map
      -> G.Defs.Lookahead.lookahead list **)

  let followLookahead x gamma nu fo =
    if nullableGamma gamma nu
    then (match G.Defs.Collections.NtMap.find x fo with
          | Some s -> G.Defs.Collections.LaSet.elements s
          | None -> [])
    else []

  (** val followEntries :
      G.Defs.CoreDefs.production ->
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.follow_map
      -> table_entry list **)

  let followEntries xp nu fo =
    fromLookaheadList xp
      (followLookahead (G.Defs.Utils.lhs xp)
        (G.Defs.Utils.rhs xp) nu fo)

  (** val entriesForProd :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.CoreDefs.production
      -> table_entry list **)

  let entriesForProd nu fi fo xp =
    app (firstEntries xp nu fi) (followEntries xp nu fo)

  (** val mkEntries' :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.CoreDefs.production
      list -> table_entry list **)

  let mkEntries' nu fi fo xps =
    flat_map (entriesForProd nu fi fo) xps

  (** val mkEntries :
      G.Defs.Collections.NtSet.t -> G.Defs.Specs.first_map ->
      G.Defs.Specs.follow_map -> G.Defs.CoreDefs.grammar ->
      table_entry list **)

  let mkEntries nu fi fo g =
    mkEntries' nu fi fo (G.Defs.CoreDefs.prods g)

  (** val ambigMessage :
      G.Defs.Lookahead.lookahead -> G.SymTy.nonterminal ->
      G.Defs.CoreDefs.symbol list -> G.Defs.CoreDefs.symbol
      list -> char list **)

  let ambigMessage la x gamma gamma' =
    append
      ('T'::('h'::('e'::(' '::('g'::('r'::('a'::('m'::('m'::('a'::('r'::(' '::('i'::('s'::(' '::('n'::('o'::('t'::(' '::('L'::('L'::('('::('1'::(')'::(';'::(' '::[]))))))))))))))))))))))))))
      (append (G.Defs.Lookahead.showLookahead la)
        (append
          (' '::('i'::('s'::(' '::('a'::(' '::('l'::('o'::('o'::('k'::('a'::('h'::('e'::('a'::('d'::(' '::('t'::('o'::('k'::('e'::('n'::('\n'::(' '::(' '::(' '::(' '::(' '::('f'::('o'::('r'::(' '::('t'::('h'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('t'::('w'::('o'::(' '::('p'::('r'::('o'::('d'::('u'::('c'::('t'::('i'::('o'::('n'::('s'::(' '::('w'::('i'::('t'::('h'::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('l'::('e'::('f'::('t'::('-'::('h'::('a'::('n'::('d'::(' '::('s'::('i'::('d'::('e'::(' '::('a'::('n'::('d'::('\n'::(' '::(' '::(' '::(' '::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::(' '::('r'::('i'::('g'::('h'::('t'::('-'::('h'::('a'::('n'::('d'::(' '::('s'::('i'::('d'::('e'::('s'::(':'::('\\'::('n'::('\\'::('n'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (append (G.Defs.Formatting.showBaseProd (x, gamma))
            (append ('\\'::('n'::[]))
              (G.Defs.Formatting.showBaseProd (x, gamma'))))))

  (** val empty_table :
      G.Defs.CoreDefs.production
      G.Defs.Collections.ParseTable.t **)

  let empty_table =
    G.Defs.Collections.ParseTable.empty

  (** val addEntry :
      table_entry -> (char list,
      G.Defs.Collections.parse_table) sum -> (char list,
      G.Defs.Collections.parse_table) sum **)

  let addEntry e = function
  | Inl msg -> Inl msg
  | Inr tbl ->
    let (xp, la) = e in
    let ExistT (x0, _) = xp in
    let (x, gamma) = x0 in
    (match G.Defs.Utils.pt_lookup x la tbl with
     | Some p ->
       let ExistT (x1, _) = p in
       let (x', gamma') = x1 in
       if L.base_production_eq_dec (x, gamma) (x', gamma')
       then Inr tbl
       else Inl (ambigMessage la x gamma gamma')
     | None -> Inr (G.Defs.Utils.pt_add x la xp tbl))

  (** val mkParseTable :
      table_entry list -> (char list,
      G.Defs.Collections.parse_table) sum **)

  let mkParseTable ps =
    fold_right addEntry (Inr empty_table) ps

  (** val dupMessage :
      G.Defs.CoreDefs.base_production -> char list **)

  let dupMessage b =
    append
      ('T'::('h'::('e'::(' '::('f'::('o'::('l'::('l'::('o'::('w'::('i'::('n'::('g'::(' '::('p'::('r'::('o'::('d'::('u'::('c'::('t'::('i'::('o'::('n'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::('s'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('t'::('i'::('m'::('e'::('s'::(' '::('i'::('n'::(' '::('t'::('h'::('e'::(' '::('g'::('r'::('a'::('m'::('m'::('a'::('r'::(':'::('\\'::('n'::('\\'::('n'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (append (G.Defs.Formatting.showBaseProd b)
        ('\\'::('n'::('\\'::('n'::('T'::('h'::('e'::(' '::('g'::('r'::('a'::('m'::('m'::('a'::('r'::(' '::('i'::('s'::(' '::('e'::('i'::('t'::('h'::('e'::('r'::(' '::('a'::('m'::('b'::('i'::('g'::('u'::('o'::('u'::('s'::(' '::('('::('i'::('f'::(' '::('t'::('h'::('e'::(' '::('p'::('r'::('o'::('d'::('u'::('c'::('t'::('i'::('o'::('n'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::('s'::(' '::('w'::('i'::('t'::('h'::(' '::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('d'::('i'::('f'::('f'::('e'::('r'::('e'::('n'::('t'::(' '::('a'::('c'::('t'::('i'::('o'::('n'::('s'::(')'::(','::(' '::('o'::('r'::(' '::('r'::('e'::('d'::('u'::('n'::('d'::('a'::('n'::('t'::(' '::('('::('i'::('f'::(' '::('i'::('t'::(' '::('a'::('p'::('p'::('e'::('a'::('r'::('s'::(' '::('m'::('u'::('l'::('t'::('i'::('p'::('l'::('e'::(' '::('t'::('i'::('m'::('e'::('s'::(' '::('w'::('i'::('t'::('h'::('\n'::(' '::(' '::(' '::(' '::(' '::(' '::(' '::(' '::('t'::('h'::('e'::(' '::('s'::('a'::('m'::('e'::(' '::('a'::('c'::('t'::('i'::('o'::('n'::(')'::('.'::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
 end

module NullableProofsFn =
 functor (G:T) ->
 struct
  module Gen = GeneratorFn(G)

  module L = LemmasFn(G)
 end

module FirstProofsFn =
 functor (G:T) ->
 struct
  module NullableProofs = NullableProofsFn(G)

  module L = LemmasFn(G)
 end

module FollowProofsFn =
 functor (G:T) ->
 struct
  module FirstProofs = FirstProofsFn(G)

  module L = LemmasFn(G)
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

  type pl_pair =
    G.Defs.CoreDefs.base_production * G.Defs.Lookahead.lookahead

  (** val plPairOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry
      ->
      G.Defs.CoreDefs.base_production * G.Defs.Lookahead.lookahead **)

  let plPairOf = function
  | (p0, la) -> let ExistT (p, _) = p0 in (p, la)

  (** val plPairsOf :
      EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.table_entry
      list ->
      (G.Defs.CoreDefs.base_production * G.Defs.Lookahead.lookahead)
      list **)

  let plPairsOf es =
    map plPairOf es

  (** val pl_pair_eq_dec : pl_pair -> pl_pair -> bool **)

  let pl_pair_eq_dec p p' =
    let (x, x0) = p in
    let (b0, l) = p' in
    if let (x1, x2) = x in
       let (n, l0) = b0 in
       if G.SymTy.nt_eq_dec x1 n
       then let rec f l1 x3 =
              match l1 with
              | [] ->
                (match x3 with
                 | [] -> true
                 | _ :: _ -> false)
              | y :: l2 ->
                (match x3 with
                 | [] -> false
                 | s :: l3 ->
                   if G.Defs.CoreDefs.symbol_rect
                        (fun t0 x4 ->
                        match x4 with
                        | G.Defs.CoreDefs.T t1 ->
                          G.SymTy.t_eq_dec t0 t1
                        | G.Defs.CoreDefs.NT _ -> false)
                        (fun n0 x4 ->
                        match x4 with
                        | G.Defs.CoreDefs.T _ -> false
                        | G.Defs.CoreDefs.NT n1 ->
                          G.SymTy.nt_eq_dec n0 n1) y s
                   then f l2 l3
                   else false)
            in f x2 l0
       else false
    then G.Defs.Lookahead.lookahead_rect (fun t0 x1 ->
           match x1 with
           | G.Defs.Lookahead.LA t1 -> G.SymTy.t_eq_dec t0 t1
           | G.Defs.Lookahead.EOF -> false) (fun x1 ->
           match x1 with
           | G.Defs.Lookahead.LA _ -> false
           | G.Defs.Lookahead.EOF -> true) x0 l
    else false
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
 end

module ParserProofsFn =
 functor (G:T) ->
 struct
  module ParserSafety = ParserSafetyFn(G)

  module L = LemmasFn(G)
 end

module Coq0_Make =
 functor (G:T) ->
 struct
  module GeneratorAndProofs = GeneratorProofsFn(G)

  module ParserAndProofs = ParserProofsFn(G)

  (** val parseTableOf :
      G.Defs.CoreDefs.grammar -> (char list,
      G.Defs.Collections.parse_table) sum **)

  let parseTableOf g =
    match findDup
            GeneratorAndProofs.EntryProofs.FollowProofs.L.base_production_eq_dec
            (G.Defs.Utils.baseProductions g) with
    | Some b ->
      Inl
        (GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.dupMessage
          b)
    | None ->
      let nu =
        GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkNullableSet
          g
      in
      let fi =
        GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkFirstMap
          g nu
      in
      let fo =
        GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkFollowMap
          g nu fi
      in
      let es =
        GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkEntries
          nu fi fo g
      in
      GeneratorAndProofs.EntryProofs.FollowProofs.FirstProofs.NullableProofs.Gen.mkParseTable
        es

  (** val parse :
      G.Defs.Collections.parse_table ->
      G.Defs.CoreDefs.symbol -> G.Defs.CoreDefs.token list ->
      (ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parse_failure,
      G.Defs.CoreDefs.symbol_semty * G.Defs.CoreDefs.token
      list) sum **)

  let parse tbl s ts =
    match ParserAndProofs.ParserSafety.ParserSoundness.ParserDefs.parseSymbol
            tbl s ts G.Defs.Collections.NtSet.empty with
    | Inl failure -> Inl failure
    | Inr p ->
      let (v, s0) = p in
      let ExistT (ts', _) = s0 in Inr (v, ts')
 end

type jvalue =
| JAssoc of (char list * jvalue) list
| JBool of bool
| JFloat of nat
| JInt of nat
| JList of jvalue list
| JNull
| JString of char list

module Json_Types =
 struct
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

  (** val terminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1 **)

  let terminal'_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | Int -> f
  | Float -> f0
  | Str -> f1
  | Tru -> f2
  | Fls -> f3
  | Null -> f4
  | LeftBrace -> f5
  | RightBrace -> f6
  | LeftBrack -> f7
  | RightBrack -> f8
  | Colon -> f9
  | Comma -> f10

  (** val terminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> terminal' -> 'a1 **)

  let terminal'_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | Int -> f
  | Float -> f0
  | Str -> f1
  | Tru -> f2
  | Fls -> f3
  | Null -> f4
  | LeftBrace -> f5
  | RightBrace -> f6
  | LeftBrack -> f7
  | RightBrack -> f8
  | Colon -> f9
  | Comma -> f10

  type terminal = terminal'

  type nonterminal' =
  | Value
  | Pairs
  | PairsTl
  | Pair
  | Elts
  | EltsTl

  (** val nonterminal'_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal'
      -> 'a1 **)

  let nonterminal'_rect f f0 f1 f2 f3 f4 = function
  | Value -> f
  | Pairs -> f0
  | PairsTl -> f1
  | Pair -> f2
  | Elts -> f3
  | EltsTl -> f4

  (** val nonterminal'_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> nonterminal'
      -> 'a1 **)

  let nonterminal'_rec f f0 f1 f2 f3 f4 = function
  | Value -> f
  | Pairs -> f0
  | PairsTl -> f1
  | Pair -> f2
  | Elts -> f3
  | EltsTl -> f4

  type nonterminal = nonterminal'

  (** val t_eq_dec : terminal -> terminal -> bool **)

  let t_eq_dec t0 t' =
    match t0 with
    | Int -> (match t' with
              | Int -> true
              | _ -> false)
    | Float -> (match t' with
                | Float -> true
                | _ -> false)
    | Str -> (match t' with
              | Str -> true
              | _ -> false)
    | Tru -> (match t' with
              | Tru -> true
              | _ -> false)
    | Fls -> (match t' with
              | Fls -> true
              | _ -> false)
    | Null -> (match t' with
               | Null -> true
               | _ -> false)
    | LeftBrace ->
      (match t' with
       | LeftBrace -> true
       | _ -> false)
    | RightBrace ->
      (match t' with
       | RightBrace -> true
       | _ -> false)
    | LeftBrack ->
      (match t' with
       | LeftBrack -> true
       | _ -> false)
    | RightBrack ->
      (match t' with
       | RightBrack -> true
       | _ -> false)
    | Colon -> (match t' with
                | Colon -> true
                | _ -> false)
    | Comma -> (match t' with
                | Comma -> true
                | _ -> false)

  (** val nt_eq_dec : nonterminal -> nonterminal -> bool **)

  let nt_eq_dec nt nt' =
    match nt with
    | Value -> (match nt' with
                | Value -> true
                | _ -> false)
    | Pairs -> (match nt' with
                | Pairs -> true
                | _ -> false)
    | PairsTl -> (match nt' with
                  | PairsTl -> true
                  | _ -> false)
    | Pair -> (match nt' with
               | Pair -> true
               | _ -> false)
    | Elts -> (match nt' with
               | Elts -> true
               | _ -> false)
    | EltsTl -> (match nt' with
                 | EltsTl -> true
                 | _ -> false)

  (** val showT : terminal -> char list **)

  let showT = function
  | Int -> 'I'::('n'::('t'::[]))
  | Float -> 'F'::('l'::('o'::('a'::('t'::[]))))
  | Str -> 'S'::('t'::('r'::('i'::('n'::('g'::[])))))
  | Tru -> 'T'::('r'::('u'::('e'::[])))
  | Fls -> 'F'::('a'::('l'::('s'::('e'::[]))))
  | Null -> 'N'::('u'::('l'::('l'::[])))
  | LeftBrace -> '{'::[]
  | RightBrace -> '}'::[]
  | LeftBrack -> '['::[]
  | RightBrack -> ']'::[]
  | Colon -> ':'::[]
  | Comma -> ','::[]

  (** val showNT : nonterminal -> char list **)

  let showNT = function
  | Value -> 'v'::('a'::('l'::('u'::('e'::[]))))
  | Pairs -> 'p'::('a'::('i'::('r'::('s'::[]))))
  | PairsTl ->
    'p'::('a'::('i'::('r'::('s'::('_'::('t'::('l'::[])))))))
  | Pair -> 'p'::('a'::('i'::('r'::[])))
  | Elts -> 'e'::('l'::('t'::('s'::[])))
  | EltsTl ->
    'e'::('l'::('t'::('s'::('_'::('t'::('l'::[]))))))

  type t_semty = __

  type nt_semty = __
 end

module G =
 struct
  module SymTy = Json_Types

  module Defs = DefsFn(SymTy)
 end

module PG = Coq0_Make(G)

(** val jsonGrammar : G.Defs.CoreDefs.grammar **)

let jsonGrammar =
  { G.Defs.CoreDefs.start = G.SymTy.Value;
    G.Defs.CoreDefs.prods = ((ExistT ((G.SymTy.Value,
    ((G.Defs.CoreDefs.T
    G.SymTy.LeftBrace) :: ((G.Defs.CoreDefs.NT
    G.SymTy.Pairs) :: ((G.Defs.CoreDefs.T
    G.SymTy.RightBrace) :: [])))),
    (Obj.magic (fun tup ->
      let (_, t0) = tup in let (prs, _) = t0 in JAssoc prs)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.LeftBrack) :: ((G.Defs.CoreDefs.NT
    G.SymTy.Elts) :: ((G.Defs.CoreDefs.T
    G.SymTy.RightBrack) :: [])))),
    (Obj.magic (fun tup ->
      let (_, t0) = tup in let (es, _) = t0 in JList es)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Str) :: [])),
    (Obj.magic (fun tup -> let (s, _) = tup in JString s)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Int) :: [])),
    (Obj.magic (fun tup -> let (n, _) = tup in JInt n)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Float) :: [])),
    (Obj.magic (fun tup -> let (n, _) = tup in JFloat n)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Tru) :: [])),
    (Obj.magic (fun _ -> JBool true)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Fls) :: [])),
    (Obj.magic (fun _ -> JBool false)))) :: ((ExistT
    ((G.SymTy.Value, ((G.Defs.CoreDefs.T
    G.SymTy.Null) :: [])),
    (Obj.magic (fun _ -> JNull)))) :: ((ExistT
    ((G.SymTy.Pairs, []),
    (Obj.magic (fun _ -> [])))) :: ((ExistT ((G.SymTy.Pairs,
    ((G.Defs.CoreDefs.NT
    G.SymTy.Pair) :: ((G.Defs.CoreDefs.NT
    G.SymTy.PairsTl) :: []))),
    (Obj.magic (fun tup ->
      let (pr, t0) = tup in let (prs, _) = t0 in pr :: prs)))) :: ((ExistT
    ((G.SymTy.PairsTl, []),
    (Obj.magic (fun _ -> [])))) :: ((ExistT
    ((G.SymTy.PairsTl, ((G.Defs.CoreDefs.T
    G.SymTy.Comma) :: ((G.Defs.CoreDefs.NT
    G.SymTy.Pair) :: ((G.Defs.CoreDefs.NT
    G.SymTy.PairsTl) :: [])))),
    (Obj.magic (fun tup ->
      let (_, t0) = tup in
      let (pr, p) = t0 in let (prs, _) = p in pr :: prs)))) :: ((ExistT
    ((G.SymTy.Pair, ((G.Defs.CoreDefs.T
    G.SymTy.Str) :: ((G.Defs.CoreDefs.T
    G.SymTy.Colon) :: ((G.Defs.CoreDefs.NT
    G.SymTy.Value) :: [])))),
    (Obj.magic (fun tup ->
      let (s, t0) = tup in
      let (_, p) = t0 in let (v, _) = p in (s, v))))) :: ((ExistT
    ((G.SymTy.Elts, []),
    (Obj.magic (fun _ -> [])))) :: ((ExistT ((G.SymTy.Elts,
    ((G.Defs.CoreDefs.NT
    G.SymTy.Value) :: ((G.Defs.CoreDefs.NT
    G.SymTy.EltsTl) :: []))),
    (Obj.magic (fun tup ->
      let (v, t0) = tup in let (vs, _) = t0 in v :: vs)))) :: ((ExistT
    ((G.SymTy.EltsTl, []),
    (Obj.magic (fun _ -> [])))) :: ((ExistT ((G.SymTy.EltsTl,
    ((G.Defs.CoreDefs.T
    G.SymTy.Comma) :: ((G.Defs.CoreDefs.NT
    G.SymTy.Value) :: ((G.Defs.CoreDefs.NT
    G.SymTy.EltsTl) :: [])))),
    (Obj.magic (fun tup ->
      let (_, t0) = tup in
      let (v, p) = t0 in let (vs, _) = p in v :: vs)))) :: []))))))))))))))))) }

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

(** val depTokenOfSimplyTypedToken :
    simply_typed_token -> G.Defs.CoreDefs.token **)

let depTokenOfSimplyTypedToken = function
| StInt n -> ExistT (G.SymTy.Int, (Obj.magic n))
| StFloat n -> ExistT (G.SymTy.Float, (Obj.magic n))
| StStr s -> ExistT (G.SymTy.Str, (Obj.magic s))
| StTru -> ExistT (G.SymTy.Tru, (Obj.magic ()))
| StFls -> ExistT (G.SymTy.Fls, (Obj.magic ()))
| StNull -> ExistT (G.SymTy.Null, (Obj.magic ()))
| StLeftBrace -> ExistT (G.SymTy.LeftBrace, (Obj.magic ()))
| StRightBrace -> ExistT (G.SymTy.RightBrace, (Obj.magic ()))
| StLeftBrack -> ExistT (G.SymTy.LeftBrack, (Obj.magic ()))
| StRightBrack -> ExistT (G.SymTy.RightBrack, (Obj.magic ()))
| StColon -> ExistT (G.SymTy.Colon, (Obj.magic ()))
| StComma -> ExistT (G.SymTy.Comma, (Obj.magic ()))
