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

(* Might need to add a "left <> right" constraint somewhere *)
Inductive firstSym {g : grammar} (x : symbol) :
  symbol -> Prop :=
| fi_nt : forall y gamma,
    In (x, gamma) g ->
      (@firstGamma g) x gamma y ->
      firstSym x y
with firstGamma {g : grammar} (x : symbol) :
       list symbol -> symbol -> Prop :=
     | fg_t : forall hd tl,
         isT hd = true ->
         firstGamma x (hd :: tl) hd
     | fg_nt_hd : forall hd sym tl,
         isNT hd = true ->
         hd <> x ->
         firstSym hd sym ->
         firstGamma x (hd :: tl) sym
     | fg_nt_tl : forall hd sym tl,
         isNT hd = true ->
         (@nullableSym g) hd ->
         firstGamma x tl sym ->
         firstGamma x (hd :: tl) sym.

Definition firstSetComplete fi g : Prop :=
  forall x y,
    (@firstSym g) x y ->
    exists xFirst,
      SymbolMap.find x fi = Some xFirst /\
      SymbolSet.In y xFirst.

Definition firstSetMinimal fi g : Prop :=
  forall x xFirst y,
    SymbolMap.find x fi = Some xFirst ->
    SymbolSet.In y xFirst ->
    (@firstSym g) x y.

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
      old_isFirstSetFor fi g nu ->
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
    isFirstSetFor fi g ->
    forallb (nullable nu) prefix = true ->
    SymbolSet.In z (first fi y) ->
    SymbolSet.In z fg.

(* To do : firstGammaMinimal *)