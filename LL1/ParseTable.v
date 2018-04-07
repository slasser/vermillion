Require Import List MSets String.
Require Import FMaps Grammar Lib.Utils.
Import ListNotations.

Inductive lookahead :=
| LA  : string -> lookahead
| EOF : lookahead.

(* sets and maps for lookahead tokens *)

Definition lookahead_eq_dec :
  forall (lk lk2 : lookahead),
    {lk = lk2} + {~lk = lk2}.
Proof. repeat decide equality. Defined.
  
Module MDT_Lookahead.
  Definition t := lookahead.
  Definition eq_dec := lookahead_eq_dec.
End MDT_Lookahead.

Module LookaheadAsDT := Make_UDT(MDT_Lookahead).
Module LookaheadSet := MSetWeakList.Make LookaheadAsDT.
Module LookaheadSetFacts := WFactsOn LookaheadAsDT LookaheadSet.
Module LookaheadSetEqProps := EqProperties LookaheadSet.

Module LookaheadMap := FMapWeakList.Make LookaheadAsDT.
Module LookaheadMapFacts := WFacts_fun LookaheadAsDT LookaheadMap.

Definition parse_table :=
  StringMap.t (LookaheadMap.t (list symbol)).

Definition parseTableLookup
           (x : string)
           (y : lookahead)
           (tbl : parse_table) : option (list symbol) :=
  match StringMap.find x tbl with
  | None      => None
  | Some tMap => LookaheadMap.find y tMap
  end.
    
(* Definition of the NULLABLE set for a given grammar *)

(* This can be simplified a little *)
Inductive nullableSym {g : grammar} : nonterminal -> Prop :=
| nullable_nt :
    forall x gamma,
      nullableProd x gamma ->
      nullableSym x
with nullableProd {g : grammar} : nonterminal -> list symbol -> Prop :=
     | nprod :
         forall x ys,
           In (x, ys) g.(productions) ->
           (forall sym,
               In sym ys ->
               sym <> NT x) ->
           nullableGamma ys ->
           nullableProd x ys
with nullableGamma {g : grammar} : list symbol -> Prop :=
     | nullable_nil :
         nullableGamma nil
     | nullable_cons :
         forall hd tl,
           nullableSym hd ->
           nullableGamma tl ->
           nullableGamma (NT hd :: tl).

Definition nullableSetComplete (nu : StringSet.t)
                               (g : grammar) : Prop :=
  forall x,
    (@nullableSym g) x ->
    StringSet.In x nu.

Definition nullableSetMinimal (nu : StringSet.t)
                              (g  : grammar) : Prop :=
  forall x,
    StringSet.In x nu ->
    (@nullableSym g) x.

Definition isNullableSetFor nu g : Prop :=
  nullableSetComplete nu g /\ nullableSetMinimal nu g.


(* Definition of the FIRST set for a given grammar *)

Inductive firstSym {g : grammar} :
  lookahead -> symbol -> Prop :=
| first_t : forall s,
    firstSym (LA s) (T s)
| first_nt : forall x y ys,
    firstProd y x ys ->
    firstSym y (NT x)
with firstProd {g : grammar} :
       lookahead -> nonterminal -> list symbol -> Prop :=
     | fprod : forall y x ys,
         In (x, ys) g.(productions) ->
         firstProd' y x ys ->
         firstProd y x ys
with firstProd' {g : grammar} :
       lookahead -> nonterminal -> list symbol -> Prop :=
     | fprod_hd : forall y x hd tl,
         NT x <> hd ->
         firstSym y hd ->
         firstProd' y x (hd :: tl)
     | fprod_tl : forall y x hd tl,
         (@nullableSym g) hd ->
         firstProd' y x tl ->
         firstProd' y x (NT hd :: tl).

Inductive firstGamma {g : grammar} :
  lookahead -> list symbol -> Prop :=
| fgamma_hd : forall y hd tl,
    (@firstSym g) y hd ->
    firstGamma y (hd :: tl)
| fgamma_tl : forall y hd tl,
    (@nullableSym g) hd ->
    firstGamma y tl ->
    firstGamma y (NT hd :: tl).

Definition firstSetComplete fi g : Prop :=
  forall x y,
    (@firstSym g) y (NT x) ->
    exists xFirst,
      StringMap.find x fi = Some xFirst /\
      LookaheadSet.In y xFirst.

Definition firstSetMinimal fi g : Prop :=
  forall x xFirst y,
    StringMap.find x fi = Some xFirst ->
    LookaheadSet.In y xFirst ->
    (@firstSym g) y (NT x).

Definition isFirstSetFor fi g : Prop :=
  firstSetComplete fi g /\ firstSetMinimal fi g.


(* Definition of the FOLLOW set for a given grammar *)

(* Remember to add EOF *)
Inductive followSym {g : grammar} : lookahead -> nonterminal -> Prop :=
| followRight :
    forall lx rx prefix suffix y,
      In (lx, (prefix ++ NT rx :: suffix)%list) g.(productions) ->
      (@firstGamma g) y suffix -> 
      followSym y rx
| followLeft :
    forall lx rx prefix suffix la,
      In (lx, (prefix ++ NT rx :: suffix)%list) g.(productions) ->
      lx <> rx -> (* Necessary? *)
      (@nullableGamma g) suffix ->
      followSym la lx ->
      followSym la rx.

Definition followSetComplete fo g : Prop :=
  forall x y,
    (@followSym g) y x ->
    exists xFollow,
      StringMap.find x fo = Some xFollow /\
      LookaheadSet.In y xFollow.

Definition followSetMinimal fo g : Prop :=
  forall x xFollow y,
    StringMap.find x fo = Some xFollow ->
    LookaheadSet.In y xFollow ->
    (@followSym g) y x.

Definition isFollowSetFor fo g : Prop :=
  followSetComplete fo g /\ followSetMinimal fo g.

Definition ptCompleteFirst tbl g : Prop :=
  forall x gamma y,
    In (x, gamma) g.(productions) ->
    (@firstGamma g) y gamma ->
    exists tMap,
      StringMap.find x tbl = Some tMap  /\
      LookaheadMap.find y tMap = Some gamma. 

Definition ptCompleteFollow tbl g : Prop :=
  forall x gamma y,
    In (x, gamma) g.(productions) ->
    (@nullableGamma g) gamma ->
    (@followSym g) y x ->
    exists tMap,
      StringMap.find x tbl  = Some tMap /\
      LookaheadMap.find y tMap = Some gamma.

Definition parseTableComplete tbl g : Prop :=
  ptCompleteFirst tbl g /\ ptCompleteFollow tbl g.

Definition parseTableMinimal tbl g : Prop :=
  forall x tMap y gamma,
    StringMap.find x tbl = Some tMap ->
    LookaheadMap.find y tMap = Some gamma ->
    (@firstProd g) y x gamma \/
    (@nullableProd g) x gamma /\ (@followSym g) y x.

Definition isParseTableFor tbl g : Prop :=
  parseTableComplete tbl g /\ parseTableMinimal tbl g.
