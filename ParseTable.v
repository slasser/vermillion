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

(* This seems like the best NULLABLE definition so far *)

Definition All (A : Set) (f : A -> Prop) (l : list A) :=
  forall a, In a l -> f a.

SearchAbout (forall (A : Set), (A -> Prop) -> list A -> Prop).
Inductive nullableSym {g : grammar} : symbol -> Prop :=
| nullable_nt :
    forall x gamma,
      In (NT x, gamma) g ->
      (forall sym,
          In sym gamma ->
          sym <> NT x) ->
      nullableGamma gamma ->
      nullableSym (NT x)
  with nullableGamma {g : grammar} : list symbol -> Prop :=
     | nullable_nil :
         nullableGamma nil
     | nullable_cons :
         forall hd tl,
           nullableSym hd ->
           nullableGamma tl ->
           nullableGamma (hd :: tl).

(* Read about creating induction schemes *)
Scheme foo := Induction for nullableSym Sort Prop
  with bar := Induction for nullableGamma Sort Prop.

Definition nullableSetComplete (nu : SymbolSet.t)
                               (g : grammar) : Prop :=
  forall x,
    (@nullableSym g) (NT x) ->
    SymbolSet.In (NT x) nu.

Definition nullableSetMinimal (nu : SymbolSet.t)
                              (g  : grammar) : Prop :=
  forall x,
    SymbolSet.In (NT x) nu ->
    (@nullableSym g) (NT x).

Definition isNullableSetFor nu g : Prop :=
  nullableSetComplete nu g /\ nullableSetMinimal nu g.

(* For future reference, here are some alternative definitions
   that didn't work out *)

Definition flawedNullableSetComplete (nu : SymbolSet.t)
                                     (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    In (x, ys) g ->
    forallb (nullable nu) ys = true ->
    SymbolSet.In x nu.

Definition flawedNullableSetMinimal (nu : SymbolSet.t)
                                    (g : grammar) : Prop :=
  forall (x : symbol),
    SymbolSet.In x nu ->
    exists (ys : list symbol),
      In (x, ys) g /\
      forallb (nullable nu) ys = true.

Definition flawedIsNullableSetFor (nu : SymbolSet.t)
                                  (g : grammar) : Prop :=
  flawedNullableSetComplete nu g /\
  flawedNullableSetMinimal nu g.

Inductive flawedSymInNullableSet {g : grammar} : symbol -> Prop :=
| nullableProd :
    forall x gamma,
      In (NT x, gamma) g ->
      (forall sym, 
          In sym gamma ->
          sym <> NT x /\ flawedSymInNullableSet sym) ->
      flawedSymInNullableSet (NT x).

(* Definition of the FIRST set for a given grammar *)


Inductive firstSym {g : grammar} :
  symbol -> symbol -> Prop :=
| first_t : forall y,
    isT y = true ->
    firstSym y y
| first_nt : forall x y ys,
    isNT x = true -> (* needed? *)
    In (x, ys) g ->
      firstProd y x ys ->
      firstSym y x
with firstProd {g : grammar} :
       symbol -> symbol -> list symbol -> Prop :=
     | fprod_hd : forall y x hd tl,
         x <> hd ->
         firstSym y hd ->
         firstProd y x (hd :: tl)
     | fprod_tl : forall y x hd tl,
         (@nullableSym g) hd ->
         firstProd y x tl ->
         firstProd y x (hd :: tl).

Inductive firstGamma {g : grammar} :
  symbol -> list symbol -> Prop :=
| fgamma_hd : forall y hd tl,
    (@firstSym g) y hd ->
    firstGamma y (hd :: tl)
| fgamma_tl : forall y hd tl,
    (@nullableSym g) hd ->
    firstGamma y tl ->
    firstGamma y (hd :: tl).

Definition firstSetComplete fi g : Prop :=
  forall x y,
    isNT x = true ->
    (@firstSym g) y x ->
    exists xFirst,
      SymbolMap.find x fi = Some xFirst /\
      SymbolSet.In y xFirst.

Definition firstSetMinimal fi g : Prop :=
  forall x xFirst y,
    SymbolMap.find x fi = Some xFirst ->
    SymbolSet.In y xFirst ->
    (@firstSym g) y x.

Definition isFirstSetFor fi g : Prop :=
  firstSetComplete fi g /\ firstSetMinimal fi g.

(* A previous attempt at defining FIRST *)
Inductive pairInFirstSet {g : grammar} {nu : SymbolSet.t} :
  symbol -> symbol -> Prop :=    
| firstPairT : forall X y prefix suffix,
    In (NT X, prefix ++ T y :: suffix) g ->
    isNullableSetFor nu g ->
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT X) (T y)
| firstPairNT : forall leftX rightX y prefix suffix,
    In (NT leftX, prefix ++ NT rightX :: suffix) g ->
    leftX <> rightX ->
    forallb (nullable nu) prefix = true ->
    pairInFirstSet (NT rightX) (T y) ->
    pairInFirstSet (NT leftX) (T y).
    
Definition old_firstSetComplete fi g nu : Prop :=
  forall X y,
    (@pairInFirstSet g nu) (NT X) (T y) ->
    exists firstX,
      SymbolMap.find (NT X) fi = Some firstX /\
      SymbolSet.In (T y) firstX.

Definition old_firstSetMinimal fi g nu : Prop :=
  forall X firstX y,
    SymbolMap.find (NT X) fi = Some firstX ->
    SymbolSet.In (T y) firstX ->
    (@pairInFirstSet g nu) (NT X) (T y).

Definition old_isFirstSetFor fi g nu : Prop :=
  old_firstSetComplete fi g nu /\ old_firstSetMinimal fi g nu.

(* Some flawed alternative approaches *)

Definition flawedFirstSetComplete fi g nu : Prop :=
  forall x y sym prefix suffix,
    In (NT x, prefix ++ sym :: suffix) g ->
    forallb (nullable nu) prefix = true ->
    SymbolSet.In (T y) (first fi sym) ->
    exists xFirst,
      SymbolMap.find (NT x) fi = Some xFirst /\
      SymbolSet.In (T y) xFirst.

Definition flawedFirstSetMinimal fi g nu : Prop :=
  forall x xFirst y,
    SymbolMap.find (NT x) fi = Some xFirst /\
    SymbolSet.In (T y) xFirst ->
    exists prefix sym suffix,
      In (NT x, prefix ++ sym :: suffix) g /\
      forallb (nullable nu) prefix = true /\
      SymbolSet.In (T y) (first fi sym).

Definition flawedIsFirstSetFor fi g nu : Prop :=
  isNullableSetFor nu g    /\
  flawedFirstSetComplete fi g nu /\
  flawedFirstSetMinimal fi g nu.

(* Definition of the FOLLOW set for a given grammar *)

Inductive followSym {g : grammar} : symbol -> symbol -> Prop :=
| followRight :
    forall lx rx prefix suffix y,
      In (lx, prefix ++ rx :: suffix) g ->
      isNT rx = true ->
      (@firstGamma g) y suffix -> 
      followSym y rx
| followLeft :
    forall lx rx prefix suffix y,
      In (lx, prefix ++ rx :: suffix) g ->
      isNT rx = true ->
      lx <> rx -> (* Should this be in the definition? *)
      (@nullableGamma g) suffix ->
      followSym y lx ->
      followSym y rx.

Definition followSetComplete fo g : Prop :=
  forall x y,
    (@followSym g) y x ->
    exists xFollow,
      SymbolMap.find x fo = Some xFollow /\
      SymbolSet.In y xFollow.

Definition followSetMinimal fo g : Prop :=
  forall x xFollow y,
    SymbolMap.find x fo = Some xFollow ->
    SymbolSet.In y xFollow ->
    (@followSym g) y x.

Definition isFollowSetFor fo g : Prop :=
  followSetComplete fo g /\ followSetMinimal fo g.

(* To do: figure out whether any of these clauses need
   "A <> B" constraints *)
Inductive pairInFollowSet
          {g : grammar}
          {nu : SymbolSet.t}
          {fi : SymbolMap.t SymbolSet.t} :
  symbol -> symbol -> Prop :=
| old_followRight :
    forall (A B : string)
           (prefix infix suffix : list symbol)
           (y z : symbol),
      In (NT A, prefix ++ NT B :: infix ++ y :: suffix) g ->
      old_isFirstSetFor fi g nu ->
      forallb (nullable nu) infix = true ->
      SymbolSet.In z (first fi y) -> (* use the relational definition of FIRST here instead? *)
      pairInFollowSet (NT B) z
| old_followLeft :
    forall (A B : string)
           (prefix suffix : list symbol)
           (y : symbol),
      In (NT A, prefix ++ NT B :: suffix) g ->
      A <> B ->
      forallb (nullable nu) suffix = true ->
      pairInFollowSet (NT A) y ->
      pairInFollowSet (NT B) y.

Definition old_followSetComplete fo g nu fi : Prop :=
  forall X y,
    (@pairInFollowSet g nu fi) (NT X) (T y) ->
    exists followX,
      SymbolMap.find (NT X) fo = Some followX /\
      SymbolSet.In (T y) followX.

Definition old_followSetMinimal fo g nu fi : Prop :=
  forall X followX y,
    SymbolMap.find (NT X) fo = Some followX ->
    SymbolSet.In (T y) followX ->
    (@pairInFollowSet g nu fi) (NT X) (T y).

Definition old_isFollowSetFor fo g nu fi : Prop :=
  old_followSetComplete fo g nu fi /\ old_followSetMinimal fo g nu fi.

(* Definition of a valid parse table for a given grammar *)

Definition ptCompleteFirst tbl g : Prop :=
  forall x gamma y,
    (@firstGamma g) y gamma ->
    exists row,
      SymbolMap.find x tbl = Some row  /\
      SymbolMap.find y row = Some (x, gamma).

Definition ptCompleteFollow tbl g : Prop :=
  forall x gamma y,
    (@nullableGamma g) gamma ->
    (@followSym g) y x ->
    exists row,
      SymbolMap.find x tbl = Some row /\
      SymbolMap.find y row = Some (x, gamma).

Definition parseTableComplete tbl g : Prop :=
  ptCompleteFirst tbl g /\ ptCompleteFollow tbl g.

Definition parseTableMinimal tbl g : Prop :=
  forall x row y gamma,
    SymbolMap.find x tbl = Some row ->
    SymbolMap.find y row = Some (x, gamma) ->
    (@firstGamma g) y gamma \/
    ( (@nullableGamma g) gamma /\ (@followSym g) y x ).

Definition isParseTableFor tbl g : Prop :=
  parseTableComplete tbl g /\ parseTableMinimal tbl g.
    