Require Import Grammar.
Require Import List.
Require Import ParserUtils.
Require Import String.
Import ListNotations.

Definition parse_table :=
  SymbolMap.t (SymbolMap.t (list symbol)).

Definition parseTableLookup
           (x : symbol)
           (y : symbol)
           (tbl : parse_table) : option (list symbol) :=
  match SymbolMap.find x tbl with
  | None      => None
  | Some tMap => SymbolMap.find y tMap
  end.
    
(* Definition of the NULLABLE set for a given grammar *)

(* This can be simplified a little *)
Inductive nullableSym {g : grammar} : symbol -> Prop :=
| nullable_nt :
    forall x gamma,
      nullableProd (NT x) gamma ->
      nullableSym (NT x)
with nullableProd {g : grammar} : symbol -> list symbol -> Prop :=
     | nprod :
         forall x ys,
           In (NT x, ys) g ->
           (forall sym,
               In sym ys ->
               sym <> NT x) ->
           nullableGamma ys ->
           nullableProd (NT x) ys
with nullableGamma {g : grammar} : list symbol -> Prop :=
     | nullable_nil :
         nullableGamma nil
     | nullable_cons :
         forall hd tl,
           nullableSym hd ->
           nullableGamma tl ->
           nullableGamma (hd :: tl).

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


(* Definition of the FIRST set for a given grammar *)


Inductive firstSym {g : grammar} :
  symbol -> symbol -> Prop :=
| first_t : forall y,
    isT y = true ->
    firstSym y y
| first_nt : forall x y ys,
    isNT x = true -> (* needed? *)
    firstProd y x ys ->
    firstSym y x
with firstProd {g : grammar} :
       symbol -> symbol -> list symbol -> Prop :=
     | fprod : forall y x ys,
         In (x, ys) g ->
         firstProd' y x ys ->
         firstProd y x ys
with firstProd' {g : grammar} :
       symbol -> symbol -> list symbol -> Prop :=
     | fprod_hd : forall y x hd tl,
         x <> hd ->
         firstSym y hd ->
         firstProd' y x (hd :: tl)
     | fprod_tl : forall y x hd tl,
         (@nullableSym g) hd ->
         firstProd' y x tl ->
         firstProd' y x (hd :: tl).

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
      lx <> rx -> (* Necessary? *)
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


(* Definition of a valid parse table for a given grammar *)


Definition ptCompleteFirst tbl g : Prop :=
  forall x gamma y,
    In (x, gamma) g ->
    (@firstGamma g) y gamma ->
    exists tMap,
      SymbolMap.find x tbl = Some tMap  /\
      SymbolMap.find y tMap = Some gamma.

Definition ptCompleteFollow tbl g : Prop :=
  forall x gamma y,
    In (x, gamma) g ->
    (@nullableGamma g) gamma ->
    (@followSym g) y x ->
    exists tMap,
      SymbolMap.find x tbl  = Some tMap /\
      SymbolMap.find y tMap = Some gamma.

Definition parseTableComplete tbl g : Prop :=
  ptCompleteFirst tbl g /\ ptCompleteFollow tbl g.

Definition parseTableMinimal tbl g : Prop :=
  forall x tMap y gamma,
    SymbolMap.find x tbl = Some tMap ->
    SymbolMap.find y tMap = Some gamma ->
    (@firstProd g) y x gamma \/
    (@nullableProd g) x gamma /\ (@followSym g) y x.

Definition isParseTableFor tbl g : Prop :=
  parseTableComplete tbl g /\ parseTableMinimal tbl g.