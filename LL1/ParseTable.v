Require Import FMaps.
Require Import List.
Require Import MSets.

Require Import Lib.Grammar.
Require Import Lib.Utils.

Import ListNotations.
Open Scope list_scope.

Inductive lookahead :=
| LA  : terminal -> lookahead
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

Module Lookahead_as_DT := Make_UDT(MDT_Lookahead).
Module LaSet := MSetWeakList.Make Lookahead_as_DT.
Module LookaheadSetFacts := WFactsOn Lookahead_as_DT LaSet.
Module LookaheadSetEqProps := EqProperties LaSet.

Module LaMap := FMapWeakList.Make Lookahead_as_DT.
Module LookaheadMapFacts := WFacts_fun Lookahead_as_DT LaMap.

Definition parse_table :=
  NtMap.t (LaMap.t (list symbol)).

Definition parseTableLookup
           (x : nonterminal)
           (y : lookahead)
           (tbl : parse_table) : option (list symbol) :=
  match NtMap.find x tbl with
  | None => None
  | Some tMap => LaMap.find y tMap
  end.

Inductive nullable_sym (g : grammar) : symbol -> Prop :=
| NullableSym : forall x ys,
    In (x, ys) g.(productions)
    -> nullable_gamma g ys
    -> nullable_sym g (NT x)
with nullable_gamma (g : grammar) : list symbol -> Prop :=
     | NullableNil  : nullable_gamma g []
     | NullableCons : forall hd tl,
         nullable_sym g hd
         -> nullable_gamma g tl
         -> nullable_gamma g (hd :: tl).

Hint Constructors nullable_sym nullable_gamma.

Scheme nullable_sym_mutual_ind := Induction for nullable_sym Sort Prop
  with nullable_gamma_mutual_ind := Induction for nullable_gamma Sort Prop.

Definition nullable_set_complete (nu : SymbolSet.t)
                                 (g  : grammar) : Prop :=
  forall x, nullable_sym g (NT x) -> SymbolSet.In (NT x) nu.

Definition nullable_set_minimal (nu : SymbolSet.t)
                                (g  : grammar) : Prop :=
  forall x, SymbolSet.In (NT x) nu -> nullable_sym g (NT x).

Definition nullable_set_for nu g : Prop :=
nullable_set_complete nu g /\ nullable_set_minimal nu g.

Inductive first_sym (g : grammar) :
  lookahead -> symbol -> Prop :=
| FirstT : forall s,
    first_sym g (LA s) (T s)
| FirstNT : forall x y la gpre gsuf,
    In (x, gpre ++ y :: gsuf) g.(productions)
    -> nullable_gamma g gpre
    -> first_sym g la y
    -> first_sym g la (NT x).

Hint Constructors first_sym.

Inductive first_gamma (g : grammar) : lookahead -> list symbol -> Prop :=
| FirstGamma : forall gpre gsuf la y,
    nullable_gamma g gpre
    -> first_sym g la y
    -> first_gamma g la (gpre ++ y :: gsuf).

Hint Constructors first_gamma.

Definition first_set_complete fi g : Prop :=
  forall x la,
    isNT x = true
    -> first_sym g la x
    -> exists xFirst,
        SymbolMap.find x fi = Some xFirst
        /\ LaSet.In la xFirst.

Definition first_set_minimal fi g : Prop :=
  forall x xFirst la,
    SymbolMap.find x fi = Some xFirst
    -> LaSet.In la xFirst
    -> first_sym g la x.

Definition first_set_for fi g : Prop :=
  first_set_complete fi g /\ first_set_minimal fi g.

Inductive follow_sym (g : grammar) : lookahead -> symbol -> Prop :=
| FollowNullable : forall sym,
    nullable_sym g sym
    -> follow_sym g EOF sym
| FollowRight : forall x1 x2 la gpre gsuf,
    In (x1, gpre ++ NT x2 :: gsuf) g.(productions)
    -> first_gamma g la gsuf
    -> follow_sym g la (NT x2)
| FollowLeft : forall x1 x2 la gpre gsuf,
    In (x1, gpre ++ NT x2 :: gsuf) g.(productions)
    -> nullable_gamma g gsuf
    -> follow_sym g la (NT x1)
    -> follow_sym g la (NT x2).

Hint Constructors follow_sym.

Definition follow_set_complete fo g : Prop :=
  forall x y,
    follow_sym g y x
    -> exists xFollow,
      SymbolMap.find x fo = Some xFollow
      /\ LaSet.In y xFollow.

Definition follow_set_minimal fo g : Prop :=
  forall x xFollow y,
    SymbolMap.find x fo = Some xFollow
    -> LaSet.In y xFollow
    -> follow_sym g y x.

Definition follow_set_for fo g : Prop :=
follow_set_complete fo g /\ follow_set_minimal fo g.

Definition lookahead_for g la x gamma :=
  In (x, gamma) g.(productions)
  /\ (first_gamma g la gamma
      \/ (nullable_gamma g gamma
          /\ follow_sym g la (NT x))).

Definition pt_minimal tbl g :=
  forall x la gamma laMap,
    NtMap.find x tbl = Some laMap
    -> LaMap.find la laMap = Some gamma
    -> lookahead_for g la x gamma.

Definition pt_complete tbl g :=
  forall x la gamma,
    lookahead_for g la x gamma
    -> exists laMap,
      NtMap.find x tbl = Some laMap
      /\ LaMap.find la laMap = Some gamma.

Definition parse_table_for (tbl : parse_table) (g : grammar) :=
  pt_minimal tbl g /\ pt_complete tbl g.

