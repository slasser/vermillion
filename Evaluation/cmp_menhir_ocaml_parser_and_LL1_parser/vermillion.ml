
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

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

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a compSpecT = compareSpecT

(** val compSpec2Type :
    'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type _ _ =
  compareSpec2Type

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

(** val nzhead : uint -> uint **)

let rec nzhead d = match d with
| D0 d0 -> nzhead d0
| _ -> d

(** val unorm : uint -> uint **)

let unorm d =
  match nzhead d with
  | Nil -> D0 Nil
  | x -> x

(** val norm : int -> int **)

let norm = function
| Pos d0 -> Pos (unorm d0)
| Neg d0 ->
  (match nzhead d0 with
   | Nil -> Pos (D0 Nil)
   | x -> Neg x)

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil -> D1 Nil
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

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
  type t = nat

  (** val zero : nat **)

  let zero =
    O

  (** val one : nat **)

  let one =
    S O

  (** val two : nat **)

  let two =
    S (S O)

  (** val succ : nat -> nat **)

  let succ x =
    S x

  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val double : nat -> nat **)

  let double n =
    add n n

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n' -> (match m with
               | O -> false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> true
    | S n' -> (match m with
               | O -> false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val min : nat -> nat -> nat **)

  let rec min n m =
    match n with
    | O -> O
    | S n' -> (match m with
               | O -> O
               | S m' -> S (min n' m'))

  (** val even : nat -> bool **)

  let rec even = function
  | O -> true
  | S n0 -> (match n0 with
             | O -> false
             | S n' -> even n')

  (** val odd : nat -> bool **)

  let odd n =
    negb (even n)

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val tail_add : nat -> nat -> nat **)

  let rec tail_add n m =
    match n with
    | O -> m
    | S n0 -> tail_add n0 (S m)

  (** val tail_addmul : nat -> nat -> nat -> nat **)

  let rec tail_addmul r n m =
    match n with
    | O -> r
    | S n0 -> tail_addmul (tail_add m r) n0 m

  (** val tail_mul : nat -> nat -> nat **)

  let tail_mul n m =
    tail_addmul O n m

  (** val of_uint_acc : uint -> nat -> nat **)

  let rec of_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 d0 ->
      of_uint_acc d0
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc)
    | D1 d0 ->
      of_uint_acc d0 (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc))
    | D2 d0 ->
      of_uint_acc d0 (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc)))
    | D3 d0 ->
      of_uint_acc d0 (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc))))
    | D4 d0 ->
      of_uint_acc d0 (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc)))))
    | D5 d0 ->
      of_uint_acc d0 (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc))))))
    | D6 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc)))))))
    | D7 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc))))))))
    | D8 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc)))))))))
    | D9 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O))))))))))
          acc))))))))))

  (** val of_uint : uint -> nat **)

  let of_uint d =
    of_uint_acc d O

  (** val to_little_uint : nat -> uint -> uint **)

  let rec to_little_uint n acc =
    match n with
    | O -> acc
    | S n0 -> to_little_uint n0 (Little.succ acc)

  (** val to_uint : nat -> uint **)

  let to_uint n =
    rev (to_little_uint n (D0 Nil))

  (** val of_int : int -> nat option **)

  let of_int d =
    match norm d with
    | Pos u -> Some (of_uint u)
    | Neg _ -> None

  (** val to_int : nat -> int **)

  let to_int n =
    Pos (to_uint n)

  (** val divmod : nat -> nat -> nat -> nat -> nat * nat **)

  let rec divmod x y q u =
    match x with
    | O -> (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x y = match y with
  | O -> y
  | S y' -> sub y' (snd (divmod x y' O y'))

  (** val gcd : nat -> nat -> nat **)

  let rec gcd a b =
    match a with
    | O -> b
    | S a' -> gcd (modulo b (S a')) (S a')

  (** val square : nat -> nat **)

  let square n =
    mul n n

  (** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

  let rec sqrt_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> sqrt_iter k' (S p) (S (S q)) (S (S q))
       | S r' -> sqrt_iter k' p q r')

  (** val sqrt : nat -> nat **)

  let sqrt n =
    sqrt_iter n O O O

  (** val log2_iter : nat -> nat -> nat -> nat -> nat **)

  let rec log2_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> log2_iter k' (S p) (S q) q
       | S r' -> log2_iter k' p (S q) r')

  (** val log2 : nat -> nat **)

  let log2 n =
    log2_iter (pred n) O (S O) O

  (** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n f x =
    match n with
    | O -> x
    | S n0 -> f (iter n0 f x)

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))

  (** val testbit : nat -> nat -> bool **)

  let rec testbit a = function
  | O -> odd a
  | S n0 -> testbit (div2 a) n0

  (** val shiftl : nat -> nat -> nat **)

  let rec shiftl a = function
  | O -> a
  | S n0 -> double (shiftl a n0)

  (** val shiftr : nat -> nat -> nat **)

  let rec shiftr a = function
  | O -> a
  | S n0 -> div2 (shiftr a n0)

  (** val bitwise :
      (bool -> bool -> bool) -> nat -> nat -> nat -> nat **)

  let rec bitwise op n a b =
    match n with
    | O -> O
    | S n' ->
      add (if op (odd a) (odd b) then S O else O)
        (mul (S (S O)) (bitwise op n' (div2 a) (div2 b)))

  (** val coq_land : nat -> nat -> nat **)

  let coq_land a b =
    bitwise (&&) a a b

  (** val coq_lor : nat -> nat -> nat **)

  let coq_lor a b =
    bitwise (||) (max a b) a b

  (** val ldiff : nat -> nat -> nat **)

  let ldiff a b =
    bitwise (fun b0 b' -> (&&) b0 (negb b')) a a b

  (** val coq_lxor : nat -> nat -> nat **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion :
      'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

  let rec recursion x f = function
  | O -> x
  | S n0 -> f n0 (recursion x f n0)

  (** val eq_dec : nat -> nat -> bool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> true
            | S _ -> false)
    | S n0 -> (match m with
               | O -> false
               | S m0 -> eq_dec n0 m0)

  (** val leb_spec0 : nat -> nat -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : nat -> nat -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__
        -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1
        -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : nat -> nat -> bool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) true false

    (** val min_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__
        -> 'a1) -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = compSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1
        -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : nat -> nat -> bool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) true false
   end

  (** val max_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : nat -> nat -> bool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : nat -> nat -> bool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : nat -> nat **)

  let sqrt_up a =
    match compare O a with
    | Lt -> S (sqrt (pred a))
    | _ -> O

  (** val log2_up : nat -> nat **)

  let log2_up a =
    match compare (S O) a with
    | Lt -> S (log2 (pred a))
    | _ -> O

  module Private_NZDiv =
   struct
   end

  (** val lcm : nat -> nat -> nat **)

  let lcm a b =
    mul a (div b (gcd a b))

  (** val eqb_spec : nat -> nat -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> nat **)

  let b2n = function
  | true -> S O
  | false -> O

  (** val setbit : nat -> nat -> nat **)

  let setbit a n =
    coq_lor a (shiftl (S O) n)

  (** val clearbit : nat -> nat -> nat **)

  let clearbit a n =
    ldiff a (shiftl (S O) n)

  (** val ones : nat -> nat **)

  let ones n =
    pred (shiftl (S O) n)

  (** val lnot : nat -> nat -> nat **)

  let lnot a n =
    coq_lxor a (ones n)
 end

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

module Nat_as_OT = Nat

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

type terminal = char list

type nonterminal = nat

type symbol =
| T of terminal
| NT of nonterminal

(** val symbol_eq_dec : symbol -> symbol -> bool **)

let symbol_eq_dec sy sy2 =
  match sy with
  | T x ->
    (match sy2 with
     | T t0 ->
       let rec f s x0 =
         match s with
         | [] -> (match x0 with
                  | [] -> true
                  | _::_ -> false)
         | a::s0 ->
           (match x0 with
            | [] -> false
            | a0::s1 ->
              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                (fun x1 x2 x3 x4 x5 x6 x7 x8 ->
                (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                  (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                  if x1
                  then if b7
                       then if x2
                            then if b8
                                 then if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                 else false
                            else if b8
                                 then false
                                 else if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                       else false
                  else if b7
                       then false
                       else if x2
                            then if b8
                                 then if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                 else false
                            else if b8
                                 then false
                                 else if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1)
                  a0)
                a)
       in f x t0
     | NT _ -> false)
  | NT x ->
    (match sy2 with
     | T _ -> false
     | NT n0 ->
       let rec f n x0 =
         match n with
         | O -> (match x0 with
                 | O -> true
                 | S _ -> false)
         | S n1 ->
           (match x0 with
            | O -> false
            | S n2 -> f n1 n2)
       in f x n0)

type production = nonterminal * symbol list

type grammar = { productions : production list;
                 start : nonterminal }

(** val productions : grammar -> production list **)

let productions x = x.productions

(** val start : grammar -> nonterminal **)

let start x = x.start

module NT_as_DT = Nat_as_OT

module NtSet = Coq_Make(NT_as_DT)

module NtMap = Make(NT_as_DT)

type tree =
| Leaf of terminal
| Node of nonterminal * tree list

type lookahead =
| LA of terminal
| EOF

type pt_key = nonterminal * lookahead

(** val pt_key_eq_dec : pt_key -> pt_key -> bool **)

let pt_key_eq_dec k k2 =
  let (x, x0) = k in
  let (n, l) = k2 in
  if let rec f n0 x1 =
       match n0 with
       | O -> (match x1 with
               | O -> true
               | S _ -> false)
       | S n1 -> (match x1 with
                  | O -> false
                  | S n2 -> f n1 n2)
     in f x n
  then (match x0 with
        | LA x1 ->
          (match l with
           | LA t0 ->
             let rec f s x2 =
               match s with
               | [] ->
                 (match x2 with
                  | [] -> true
                  | _::_ -> false)
               | a::s0 ->
                 (match x2 with
                  | [] -> false
                  | a2::s1 ->
                    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                      (fun x3 x4 x5 x6 x7 x8 x9 x10 ->
                      (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                        (fun b8 b9 b10 b11 b12 b13 b14 b15 ->
                        if x3
                        then if b8
                             then if x4
                                  then if b9
                                       then if x5
                                            then if b10
                                                 then 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                 else false
                                            else if b10
                                                 then false
                                                 else 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                       else false
                                  else if b9
                                       then false
                                       else if x5
                                            then if b10
                                                 then 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                 else false
                                            else if b10
                                                 then false
                                                 else 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                             else false
                        else if b8
                             then false
                             else if x4
                                  then if b9
                                       then if x5
                                            then if b10
                                                 then 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                 else false
                                            else if b10
                                                 then false
                                                 else 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                       else false
                                  else if b9
                                       then false
                                       else if x5
                                            then if b10
                                                 then 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                 else false
                                            else if b10
                                                 then false
                                                 else 
                                                   if x6
                                                   then 
                                                    if b11
                                                    then 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                   else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b12
                                                    then 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b13
                                                    then 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x9
                                                    then 
                                                    if b14
                                                    then 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    if x10
                                                    then 
                                                    if b15
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b15
                                                    then false
                                                    else 
                                                    f s0 s1)
                        a2)
                      a)
             in f x1 t0
           | EOF -> false)
        | EOF -> (match l with
                  | LA _ -> false
                  | EOF -> true))
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

type parse_table = symbol list ParseTable.t

(** val lookahead_eq_dec : lookahead -> lookahead -> bool **)

let lookahead_eq_dec lk lk2 =
  match lk with
  | LA x ->
    (match lk2 with
     | LA t0 ->
       let rec f s x0 =
         match s with
         | [] -> (match x0 with
                  | [] -> true
                  | _::_ -> false)
         | a::s0 ->
           (match x0 with
            | [] -> false
            | a0::s1 ->
              (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                (fun x1 x2 x3 x4 x5 x6 x7 x8 ->
                (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
                  (fun b7 b8 b9 b10 b11 b12 b13 b14 ->
                  if x1
                  then if b7
                       then if x2
                            then if b8
                                 then if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                 else false
                            else if b8
                                 then false
                                 else if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                       else false
                  else if b7
                       then false
                       else if x2
                            then if b8
                                 then if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                 else false
                            else if b8
                                 then false
                                 else if x3
                                      then if b9
                                           then if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                           else false
                                      else if b9
                                           then false
                                           else if x4
                                                then 
                                                  if b10
                                                  then 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                  else false
                                                else 
                                                  if b10
                                                  then false
                                                  else 
                                                    if x5
                                                    then 
                                                    if b11
                                                    then 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b11
                                                    then false
                                                    else 
                                                    if x6
                                                    then 
                                                    if b12
                                                    then 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b12
                                                    then false
                                                    else 
                                                    if x7
                                                    then 
                                                    if b13
                                                    then 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b13
                                                    then false
                                                    else 
                                                    if x8
                                                    then 
                                                    if b14
                                                    then 
                                                    f s0 s1
                                                    else false
                                                    else 
                                                    if b14
                                                    then false
                                                    else 
                                                    f s0 s1)
                  a0)
                a)
       in f x t0
     | EOF -> false)
  | EOF -> (match lk2 with
            | LA _ -> false
            | EOF -> true)

module MDT_Lookahead =
 struct
  type t = lookahead

  (** val eq_dec : lookahead -> lookahead -> bool **)

  let eq_dec =
    lookahead_eq_dec
 end

module Lookahead_as_DT = Make_UDT(MDT_Lookahead)

module LaSet = Coq_Make(Lookahead_as_DT)

(** val pt_lookup :
    nonterminal -> lookahead -> parse_table -> symbol list
    option **)

let pt_lookup x la tbl =
  ParseTable.find (x, la) tbl

(** val pt_add :
    nonterminal -> lookahead -> symbol list -> parse_table ->
    parse_table **)

let pt_add x la gamma tbl =
  ParseTable.add (x, la) gamma tbl

type nullable_set = NtSet.t

type first_map = LaSet.t NtMap.t

type follow_map = LaSet.t NtMap.t

(** val peek : terminal list -> lookahead **)

let peek = function
| [] -> EOF
| token :: _ -> LA token

(** val nullableGamma : symbol list -> NtSet.t -> bool **)

let rec nullableGamma gamma nu =
  match gamma with
  | [] -> true
  | s :: gamma' ->
    (match s with
     | T _ -> false
     | NT x ->
       if NtSet.mem x nu
       then nullableGamma gamma' nu
       else false)

(** val updateNu : production -> NtSet.t -> NtSet.t **)

let updateNu p nu =
  let (x, gamma) = p in
  if nullableGamma gamma nu then NtSet.add x nu else nu

(** val nullablePass :
    production list -> NtSet.t -> NtSet.t **)

let nullablePass ps nu =
  fold_right updateNu nu ps

(** val mkNullableSet'_func :
    (production list, NtSet.t) sigT -> NtSet.t **)

let rec mkNullableSet'_func x =
  let ps = projT1 x in
  let nu = projT2 x in
  let mkNullableSet'0 = fun ps0 nu0 ->
    mkNullableSet'_func (ExistT (ps0, nu0))
  in
  let nu' = nullablePass ps nu in
  if NtSet.eq_dec nu nu' then nu else mkNullableSet'0 ps nu'

(** val mkNullableSet' :
    production list -> NtSet.t -> NtSet.t **)

let mkNullableSet' ps nu =
  mkNullableSet'_func (ExistT (ps, nu))

(** val mkNullableSet : grammar -> NtSet.t **)

let mkNullableSet g =
  mkNullableSet' g.productions NtSet.empty

(** val nullableSym : symbol -> NtSet.t -> bool **)

let nullableSym sym nu =
  match sym with
  | T _ -> false
  | NT x -> NtSet.mem x nu

(** val findOrEmpty : nonterminal -> first_map -> LaSet.t **)

let findOrEmpty x fi =
  match NtMap.find x fi with
  | Some s -> s
  | None -> LaSet.empty

(** val firstSym : symbol -> first_map -> LaSet.t **)

let firstSym sym fi =
  match sym with
  | T y -> LaSet.singleton (LA y)
  | NT x -> findOrEmpty x fi

(** val firstGamma :
    symbol list -> nullable_set -> first_map -> LaSet.t **)

let rec firstGamma gamma nu fi =
  match gamma with
  | [] -> LaSet.empty
  | sym :: gamma' ->
    if nullableSym sym nu
    then LaSet.union (firstSym sym fi)
           (firstGamma gamma' nu fi)
    else firstSym sym fi

(** val updateFi :
    nullable_set -> production -> first_map -> first_map **)

let updateFi nu p fi =
  let (x, gamma) = p in
  let fg = firstGamma gamma nu fi in
  let xFirst = findOrEmpty x fi in
  let xFirst' = LaSet.union fg xFirst in
  if LaSet.eq_dec xFirst xFirst'
  then fi
  else NtMap.add x xFirst' fi

(** val firstPass :
    production list -> nullable_set -> first_map -> first_map **)

let firstPass ps nu fi =
  fold_right (updateFi nu) fi ps

(** val first_map_equiv_dec :
    first_map -> first_map -> bool **)

let first_map_equiv_dec m m' =
  let b = NtMap.equal LaSet.equal m m' in
  if b then true else false

(** val mkFirstMap'_func :
    (production list, (nullable_set, (first_map, __) sigT)
    sigT) sigT -> first_map **)

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
    production list -> nullable_set -> first_map -> first_map **)

let mkFirstMap' ps nu fi =
  mkFirstMap'_func (ExistT (ps, (ExistT (nu, (ExistT (fi,
    __))))))

(** val empty_fi : LaSet.t NtMap.t **)

let empty_fi =
  NtMap.empty

(** val mkFirstMap : grammar -> nullable_set -> first_map **)

let mkFirstMap g nu =
  let ps = g.productions in mkFirstMap' ps nu empty_fi

(** val updateFo' :
    nullable_set -> first_map -> nonterminal -> symbol list
    -> follow_map -> follow_map **)

let rec updateFo' nu fi lx gamma fo =
  match gamma with
  | [] -> fo
  | s :: gamma' ->
    (match s with
     | T _ -> updateFo' nu fi lx gamma' fo
     | NT rx ->
       let fo' = updateFo' nu fi lx gamma' fo in
       let lSet = findOrEmpty lx fo' in
       let rSet = firstGamma gamma' nu fi in
       let additions =
         if nullableGamma gamma' nu
         then LaSet.union lSet rSet
         else rSet
       in
       (match NtMap.find rx fo' with
        | Some rxFollow ->
          if LaSet.subset additions rxFollow
          then fo'
          else let rxFollow' = LaSet.union rxFollow additions
               in
               NtMap.add rx rxFollow' fo'
        | None ->
          if LaSet.is_empty additions
          then fo'
          else NtMap.add rx additions fo'))

(** val updateFo :
    nullable_set -> first_map -> production -> follow_map ->
    follow_map **)

let updateFo nu fi p fo =
  let (x, gamma) = p in updateFo' nu fi x gamma fo

(** val followPass :
    production list -> nullable_set -> first_map ->
    follow_map -> follow_map **)

let followPass ps nu fi fo =
  fold_right (updateFo nu fi) fo ps

(** val follow_map_equiv_dec :
    first_map -> first_map -> bool **)

let follow_map_equiv_dec =
  first_map_equiv_dec

(** val mkFollowMap'_func :
    (grammar, (nullable_set, (first_map, (__, (follow_map,
    __) sigT) sigT) sigT) sigT) sigT -> follow_map **)

let rec mkFollowMap'_func x =
  let g = projT1 x in
  let nu = projT1 (projT2 x) in
  let fi = projT1 (projT2 (projT2 x)) in
  let fo = projT1 (projT2 (projT2 (projT2 (projT2 x)))) in
  let mkFollowMap'0 = fun g0 nu0 fi0 fo0 ->
    mkFollowMap'_func (ExistT (g0, (ExistT (nu0, (ExistT
      (fi0, (ExistT (__, (ExistT (fo0, __))))))))))
  in
  let fo' = followPass g.productions nu fi fo in
  if follow_map_equiv_dec fo fo'
  then fo
  else mkFollowMap'0 g nu fi fo'

(** val mkFollowMap' :
    grammar -> nullable_set -> first_map -> follow_map ->
    follow_map **)

let mkFollowMap' g nu fi fo =
  mkFollowMap'_func (ExistT (g, (ExistT (nu, (ExistT (fi,
    (ExistT (__, (ExistT (fo, __))))))))))

(** val initial_fo : grammar -> LaSet.t NtMap.t **)

let initial_fo g =
  NtMap.add g.start (LaSet.singleton EOF) NtMap.empty

(** val mkFollowMap :
    grammar -> nullable_set -> first_map -> follow_map **)

let mkFollowMap g nu fi =
  mkFollowMap' g nu fi (initial_fo g)

type table_entry = (nonterminal * lookahead) * symbol list

(** val fromLookaheadList :
    nonterminal -> symbol list -> lookahead list ->
    table_entry list **)

let fromLookaheadList x gamma las =
  map (fun la -> ((x, la), gamma)) las

(** val firstGamma' :
    symbol list -> NtSet.t -> first_map -> lookahead list **)

let rec firstGamma' gamma nu fi =
  match gamma with
  | [] -> []
  | s :: gamma' ->
    (match s with
     | T y -> (LA y) :: []
     | NT x ->
       let xFirst =
         match NtMap.find x fi with
         | Some s0 -> LaSet.elements s0
         | None -> []
       in
       if NtSet.mem x nu
       then app xFirst (firstGamma' gamma' nu fi)
       else xFirst)

(** val firstEntries :
    nonterminal -> symbol list -> NtSet.t -> first_map ->
    table_entry list **)

let firstEntries x gamma nu fi =
  fromLookaheadList x gamma (firstGamma' gamma nu fi)

(** val followLookahead :
    NtMap.key -> symbol list -> NtSet.t -> LaSet.t NtMap.t ->
    LaSet.elt list **)

let followLookahead x gamma nu fo =
  if nullableGamma gamma nu
  then (match NtMap.find x fo with
        | Some s -> LaSet.elements s
        | None -> [])
  else []

(** val followEntries :
    nonterminal -> symbol list -> NtSet.t -> LaSet.t NtMap.t
    -> table_entry list **)

let followEntries x gamma nu fo =
  fromLookaheadList x gamma (followLookahead x gamma nu fo)

(** val entriesForProd :
    NtSet.t -> first_map -> LaSet.t NtMap.t -> production ->
    table_entry list **)

let entriesForProd nu fi fo = function
| (x, gamma) ->
  app (firstEntries x gamma nu fi)
    (followEntries x gamma nu fo)

(** val mkEntries' :
    NtSet.t -> first_map -> LaSet.t NtMap.t -> production
    list -> table_entry list **)

let mkEntries' nu fi fo ps =
  flat_map (entriesForProd nu fi fo) ps

(** val mkEntries :
    NtSet.t -> first_map -> LaSet.t NtMap.t -> grammar ->
    table_entry list **)

let mkEntries nu fi fo g =
  mkEntries' nu fi fo g.productions

(** val empty_table : symbol list ParseTable.t **)

let empty_table =
  ParseTable.empty

(** val addEntry :
    table_entry -> parse_table option -> parse_table option **)

let addEntry p = function
| Some tbl ->
  let (p0, gamma) = p in
  let (x, la) = p0 in
  (match pt_lookup x la tbl with
   | Some gamma' ->
     if list_eq_dec symbol_eq_dec gamma gamma'
     then Some tbl
     else None
   | None -> Some (pt_add x la gamma tbl))
| None -> None

(** val mkParseTable :
    table_entry list -> parse_table option **)

let mkParseTable ps =
  fold_right addEntry (Some empty_table) ps

(** val ptlk_dec :
    nonterminal -> lookahead -> parse_table -> (__, symbol
    list) sum **)

let ptlk_dec x la tbl =
  let o = pt_lookup x la tbl in
  (match o with
   | Some l -> Inr l
   | None -> Inl __)

type parse_failure =
| Reject of char list * char list list
| LeftRec of nonterminal * NtSet.t * char list list

(** val mem_dec : nonterminal -> NtSet.t -> bool **)

let mem_dec x s =
  let b = NtSet.mem x s in if b then true else false

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

(** val parse_nf :
    parse_table -> symbol -> char list list -> NtSet.t ->
    (parse_failure, tree * (char list list, char list
    length_lt_eq) sigT) sum **)

let rec parse_nf tbl sym input vis =
  match sym with
  | T a ->
    (match input with
     | [] ->
       Inl (Reject
         (('i'::('n'::('p'::('u'::('t'::(' '::('e'::('x'::('h'::('a'::('u'::('s'::('t'::('e'::('d'::[]))))))))))))))),
         input))
     | token :: input' ->
       if string_dec a token
       then Inr ((Leaf a), (ExistT (input',
              (length_lt_eq_cons input token input'))))
       else Inl (Reject
              (('t'::('o'::('k'::('e'::('n'::(' '::('m'::('i'::('s'::('m'::('a'::('t'::('c'::('h'::[])))))))))))))),
              input)))
  | NT x ->
    (match ptlk_dec x (peek input) tbl with
     | Inl _ ->
       Inl (Reject
         (('l'::('o'::('o'::('k'::('u'::('p'::(' '::('f'::('a'::('i'::('l'::('u'::('r'::('e'::[])))))))))))))),
         input))
     | Inr s ->
       if mem_dec x vis
       then Inl (LeftRec (x, vis, input))
       else (match parseForest_nf tbl s input
                     (NtSet.add x vis) with
             | Inl pfail -> Inl pfail
             | Inr p ->
               let (sts, s0) = p in Inr ((Node (x, sts)), s0)))

(** val parseForest_nf :
    parse_table -> symbol list -> char list list -> NtSet.t
    -> (parse_failure, tree list * (char list list, char list
    length_lt_eq) sigT) sum **)

and parseForest_nf tbl gamma input vis =
  match gamma with
  | [] ->
    Inr ([], (ExistT (input, (length_lt_eq_refl input))))
  | sym :: gamma' ->
    (match parse_nf tbl sym input vis with
     | Inl pfail -> Inl pfail
     | Inr p ->
       let (lSib, s) = p in
       let ExistT (input', hle) = s in
       if hle
       then (match parseForest_nf tbl gamma' input'
                     NtSet.empty with
             | Inl pfail -> Inl pfail
             | Inr p0 ->
               let (rSibs, s0) = p0 in
               let ExistT (input'', hle'') = s0 in
               Inr ((lSib :: rSibs), (ExistT (input'',
               (length_lt_eq_trans input'' input' input hle''
                 hle)))))
       else (match parseForest_nf tbl gamma' input vis with
             | Inl pfail -> Inl pfail
             | Inr p0 ->
               let (rSibs, s0) = p0 in
               Inr ((lSib :: rSibs), s0)))

(** val parse_wrapper :
    parse_table -> symbol -> char list list ->
    (parse_failure, tree * (char list list, char list
    length_lt_eq) sigT) sum **)

let parse_wrapper tbl sym input =
  parse_nf tbl sym input NtSet.empty

(** val parseTableOf : grammar -> parse_table option **)

let parseTableOf g =
  let nu = mkNullableSet g in
  let fi = mkFirstMap g nu in
  let fo = mkFollowMap g nu fi in
  let es = mkEntries nu fi fo g in mkParseTable es
