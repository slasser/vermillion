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

Definition nullableSetComplete (nu : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    In (x, ys) g ->
    forallb (nullable nu) ys = true ->
    SymbolSet.In x nu.

Definition nullableSetMinimal (nu : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol),
    SymbolSet.In x nu ->
    exists (ys : list symbol),
      In (x, ys) g /\
      forallb (nullable nu) ys = true.

Definition isNullableSetFor (nu : SymbolSet.t) (g : grammar) : Prop :=
  nullableSetComplete nu g /\ nullableSetMinimal nu g.

(* Definition of the FIRST set for a given grammar *)



Definition firstSetComplete fi g nu : Prop :=
  forall x y z prefix suffix,
    In (x, prefix ++ y :: suffix) g ->
    x <> y ->
    forallb (nullable nu) prefix = true ->
    SymbolSet.In z (first fi y) ->
    SymbolSet.In z (first fi x).
Print firstSetComplete.

Definition firstSetMinimal fi g nu : Prop :=
  forall x z prefix suffix,
    SymbolSet.In z (first fi x) ->
    exists y,
      In (x, prefix ++ y :: suffix) g /\
      x <> y /\
      forallb (nullable nu) prefix = true /\
      SymbolSet.In z (first fi y).

Definition isFirstSetFor fi g nu : Prop :=
  isNullableSetFor nu g /\ firstSetComplete fi g nu /\ firstSetMinimal fi g nu.

(* Previous version, which uses the relational definition of FIRST *)
(*

Inductive pairInFirstSet {g : grammar} {nu : SymbolSet.t} :
  symbol -> symbol -> Prop :=    
| firstT : forall X y prefix suffix,
    In (NT X, prefix ++ T y :: suffix) g ->
    isNullableSetFor nu g -> (* move to main theorem? *)
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT X) (T y)
| firstNT : forall leftX rightX y prefix suffix,
    In (NT leftX, prefix ++ NT rightX :: suffix) g ->
    leftX <> rightX ->
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT rightX) (T y) ->
    pairInFirstSet (NT leftX) (T y).
    
Definition firstSetComplete fi g nu : Prop :=
  forall X y,
    (@pairInFirstSet g nu) (NT X) (T y) ->
    exists firstX,
      SymbolMap.find (NT X) fi = Some firstX /\
      SymbolSet.In (T y) firstX.

Definition firstSetMinimal fi g nu : Prop :=
  forall X firstX y,
    SymbolMap.find (NT X) fi = Some firstX ->
    SymbolSet.In (T y) firstX ->
    (@pairInFirstSet g nu) (NT X) (T y).

Definition isFirstSetFor fi g nu : Prop :=
  firstSetComplete fi g nu /\ firstSetMinimal fi g nu.
*)

(* Definition of the FOLLOW set for a given grammar *)

(* To do: figure out whether any of these clauses need
   "A <> B" constraints *)
Inductive pairInFollowSet
          {g : grammar}
          {nu : SymbolSet.t}
          {fi : SymbolMap.t SymbolSet.t} :
  symbol -> symbol -> Prop :=
| followRight :
    forall (A B : string)
           (prefix infix suffix : list symbol)
           (y z : symbol),
      In (NT A, prefix ++ NT B :: infix ++ y :: suffix) g ->
      isFirstSetFor fi g nu ->
      forallb (nullable nu) infix = true ->
      SymbolSet.In z (first fi y) -> (* use the relational definition of FIRST here instead? *)
      pairInFollowSet (NT B) z
| followLeft :
    forall (A B : string)
           (prefix suffix : list symbol)
           (y : symbol),
      In (NT A, prefix ++ NT B :: suffix) g ->
      A <> B ->
      forallb (nullable nu) suffix = true ->
      pairInFollowSet (NT A) y ->
      pairInFollowSet (NT B) y.

(* 
| followRightT : forall (A B y : string)
                        (prefix infix suffix : list symbol),
    In (NT A, prefix ++ NT B :: infix ++ T y :: suffix) g ->
    isFirstSetFor fi g nu ->
    forallb (nullable nu) infix = true ->
    pairInFollowSet (NT B) (T y)
| followRightNT : forall (A B C y : string)
                         (firstC  : SymbolSet.t)
                         (prefix infix suffix : list symbol),
    In (NT A, prefix ++ NT B :: infix ++ NT C :: suffix) g ->
    isFirstSetFor fi g nu ->
    forallb (nullable nu) infix = true ->
    SymbolMap.find (NT C) fi = Some firstC ->
    SymbolSet.In (T y) firstC ->
    pairInFollowSet (NT B) (T y)
*)

Definition followSetComplete fo g nu fi : Prop :=
  forall X y,
    (@pairInFollowSet g nu fi) (NT X) (T y) ->
    exists followX,
      SymbolMap.find (NT X) fo = Some followX /\
      SymbolSet.In (T y) followX.

Definition followSetMinimal fo g nu fi : Prop :=
  forall X followX y,
    SymbolMap.find (NT X) fo = Some followX ->
    SymbolSet.In (T y) followX ->
    (@pairInFollowSet g nu fi) (NT X) (T y).

Definition isFollowSetFor fo g nu fi : Prop :=
  followSetComplete fo g nu fi /\ followSetMinimal fo g nu fi.

(* Definition of firstGamma for a production *)

Definition firstGammaComplete
           {g : grammar}
           {nu : SymbolSet.t}
           {fi : SymbolMap.t SymbolSet.t}
           (fg : SymbolSet.t) X ys : Prop :=
  forall prefix y z suffix,
    prefix ++ y :: suffix = ys ->
    In (NT X, ys) g ->
    isNullableSetFor nu g ->
    isFirstSetFor fi g nu ->
    forallb (nullable nu) prefix = true ->
    SymbolSet.In z (first fi y) ->
    SymbolSet.In z fg.

(* To do : firstGammaMinimal *)