Require Import Grammar.
Require Import List.
Require Import ParserUtils.
Require Import String.
Import ListNotations.

Definition parse_table := SymbolMap.t (SymbolMap.t (list production)).

Definition parseTableLookup (nt : symbol)
           (t : symbol) (pt : parse_table) : option production :=
  match SymbolMap.find nt pt with
  | None    => None
  | Some ma => match SymbolMap.find t ma with
               | None                  => None
               | Some nil              => None
               | Some (p1 :: p2 :: ps) => None
               | Some [p]              =>
                 let (x, ys) := p in Some (x, ys)
               end
  end.

(* Definition of the NULLABLE set for a given grammar *)

Definition nSetComplete (nSet : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    In (x, ys) g ->
    forallb (nullable nSet) ys = true ->
    SymbolSet.In x nSet.

Definition nSetMinimal (nSet : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    SymbolSet.In x nSet ->
    exists (ys : list symbol),
      In (x, ys) g /\
      forallb (nullable nSet) ys = true.

Definition isNullableSetFor (nSet : SymbolSet.t) (g : grammar) : Prop :=
  nSetComplete nSet g /\ nSetMinimal nSet g.

(* Definition of the FIRST set for a given grammar *)

Inductive pairInFirstSet {g : grammar} {nu : SymbolSet.t} :
  symbol -> symbol -> Prop :=
| firstT : forall X y prefix suffix,
    In (NT X, prefix ++ T y :: suffix) g ->
    isNullableSetFor nu g -> (* move to main theorem? *)
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT X) (T y)
| firstNT : forall leftX rightX y prefix suffix,
    In (NT leftX, prefix ++ NT rightX :: suffix) g ->
    isNullableSetFor nu g -> (* move to main theorem? *)
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT rightX) (T y) ->
    pairInFirstSet (NT leftX) (T y).

(* Fatally flawed! *)
Definition isFirstSetFor fi g nu : Prop :=
  forall X firstX y,
    SymbolMap.find (NT X) fi = Some firstX ->
    SymbolSet.In (T y) firstX <->
    (@pairInFirstSet g nu) (NT X) (T y).

(* Definition of the FOLLOW set for a given grammar *)

Inductive pairInFollowSet
          {g : grammar}
          {nu : SymbolSet.t}
          {fi : SymbolMap.t SymbolSet.t} :
          symbol -> symbol -> Prop :=
| followRight : forall (X1 X2 y : string)
                       (prefix infix suffix : list symbol)
                       (sym : symbol),
    In (NT X1, prefix ++ (NT X2) :: infix ++ sym :: suffix) g ->
    isFirstSetFor fi g nu ->
    forallb (nullable nu) infix = true ->
    SymbolSet.In (T y) (first fi sym) ->
    pairInFollowSet (NT X2) (T y)
| followLeft : forall (X1 X2 y : string)
                      (prefix suffix : list symbol),
    In (NT X1, prefix ++ (NT X2) :: suffix) g ->
    isFirstSetFor fi g nu ->
    forallb (nullable nu) suffix = true ->
    pairInFollowSet (NT X1) (T y) ->
    pairInFollowSet (NT X2) (T y).

Definition isFollowSetFor fo g nu fi : Prop :=
  forall X followX y,
    SymbolMap.find (NT X) fo = Some followX ->
    SymbolSet.In (T y) followX ->
    (@pairInFollowSet g nu fi) (NT X) (T y).