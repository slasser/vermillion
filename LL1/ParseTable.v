Require Import List MSets String.
Require Import FMaps Grammar Lib.Utils.
Import ListNotations.
Open Scope list_scope.

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
  | None => None
  | Some tMap => LookaheadMap.find y tMap
  end.

(* Changed nullableSym from nonterminal to symbol *)
Inductive nullableProd {g : grammar} :
  symbol -> list symbol -> Prop :=
| NuProd :
    forall x ys,
      In (x, ys) g.(productions)
      -> nullableGamma ys
      -> nullableProd (NT x) ys
with nullableGamma {g : grammar} :
       list symbol -> Prop :=
     | NuNil :
         nullableGamma nil
     | NuCons :
         forall x tl,
           nullableSym (NT x)
           -> nullableGamma tl
           -> nullableGamma (NT x :: tl)
with nullableSym {g : grammar} :
       symbol -> Prop :=
     | NuSym :
         forall sym ys,
           nullableProd sym ys
           -> nullableSym sym.

Inductive firstProd {g : grammar} :
    lookahead -> symbol -> list symbol -> Prop :=
| FiProd : forall la x gamma,
    In (x, gamma) g.(productions)
    -> firstGamma la gamma
    -> firstProd la (NT x) gamma
with firstGamma {g : grammar} :
       lookahead -> list symbol -> Prop :=
     | FiGammaHd : forall la hd tl,
         firstSym la hd ->
         firstGamma la (hd :: tl)
     | FiGammaTl : forall la x tl,
         (@nullableSym g) (NT x) ->
         firstGamma la tl ->
         firstGamma la (NT x :: tl)
with firstSym {g : grammar} :
       lookahead -> symbol -> Prop :=
| FiT : forall s,
    firstSym (LA s) (T s)
| FiNT : forall la sym gamma,
    firstProd la sym gamma ->
    firstSym la sym.

Scheme firstProd_mutual_ind := Induction for firstProd Sort Prop
  with firstGamma_mutual_ind := Induction for firstGamma Sort Prop
  with firstSym_mutual_ind := Induction for firstSym Sort Prop.

Inductive followProd {g : grammar} :
  lookahead -> symbol -> list symbol -> Prop :=
| FoProd :
    forall la x gamma,
      In (x, gamma) g.(productions)
      -> followSym la (NT x)
      -> followProd la (NT x) gamma
with followSym {g : grammar} :
       lookahead -> symbol -> Prop :=
     | FoNu :
         forall sym gamma,
           (@nullableProd g) sym gamma
           -> followSym EOF sym
     | FoRight :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@firstGamma g) la suffix
           -> followSym la (NT x2)
     | FoLeft :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@nullableGamma g) suffix
           -> followSym la (NT x1)
           -> followSym la (NT x2).

Scheme followProd_mutual_ind := Induction for firstProd Sort Prop
  with followSym_mutual_ind := Induction for firstSym Sort Prop.

Definition isLookaheadFor {g} la sym gamma :=
  (@firstProd g) la sym gamma
  \/ (@nullableProd g) sym gamma
     /\ (@followProd g) la sym gamma.

Definition ptMinimal tbl g :=
  forall x la gamma laMap,
    StringMap.find x tbl = Some laMap
    -> LookaheadMap.find la laMap = Some gamma
    -> (@isLookaheadFor g) la (NT x) gamma.

Definition ptComplete tbl g :=
  forall x la gamma,
    (@isLookaheadFor g) la (NT x) gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.

Definition isParseTableFor (tbl : parse_table) (g : grammar) :=
  ptMinimal tbl g /\ ptComplete tbl g.
