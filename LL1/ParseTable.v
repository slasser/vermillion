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

Definition pt_key := (nonterminal * lookahead)%type.

Definition pt_key_eq_dec :
  forall k k2 : pt_key,
    {k = k2} + {k <> k2}.
Proof. repeat decide equality. Defined.

Module MDT_PtKey.
  Definition t := pt_key.
  Definition eq_dec := pt_key_eq_dec.
End MDT_PtKey.

Module PtKey_as_DT := Make_UDT(MDT_PtKey).

Module ParseTable := FMapWeakList.Make PtKey_as_DT.

Module ParseTableFacts := WFacts_fun PtKey_as_DT ParseTable.

Definition parse_table := ParseTable.t (list symbol).

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
Module LaSetFacts := WFactsOn Lookahead_as_DT LaSet.
Module LaSetEqProps := EqProperties LaSet.

Module LaMap := FMapWeakList.Make Lookahead_as_DT.
Module LaMapFacts := WFacts_fun Lookahead_as_DT LaMap.

Definition pt_lookup
           (x   : nonterminal)
           (la  : lookahead)
           (tbl : parse_table) : option (list symbol) :=
  ParseTable.find (x, la) tbl.

Definition pt_add
           (x : nonterminal)
           (la : lookahead)
           (gamma : list symbol)
           (tbl : parse_table) : parse_table :=
  ParseTable.add (x, la) gamma tbl.                                            

Inductive nullable_sym (g : grammar) : symbol -> Prop :=
| NullableSym : forall (x : nonterminal) (ys : list symbol),
    In (x, ys) g.(productions) -> nullable_gamma g ys -> nullable_sym g (NT x)
with nullable_gamma (g : grammar) : list symbol -> Prop :=
     | NullableNil  : nullable_gamma g []
     | NullableCons : forall (hd : symbol) (tl : list symbol),
         nullable_sym g hd -> nullable_gamma g tl -> nullable_gamma g (hd :: tl).

Hint Constructors nullable_sym nullable_gamma.

Scheme nullable_sym_mutual_ind := Induction for nullable_sym Sort Prop
  with nullable_gamma_mutual_ind := Induction for nullable_gamma Sort Prop.

Definition nullable_set := NtSet.t.

Definition nullable_set_sound (nu : nullable_set) (g  : grammar) : Prop :=
  forall (x : nonterminal), NtSet.In x nu -> nullable_sym g (NT x).

Definition nullable_set_complete (nu : nullable_set) (g  : grammar) : Prop :=
  forall (x : nonterminal), nullable_sym g (NT x) -> NtSet.In x nu.

Definition nullable_set_for (nu : nullable_set) (g : grammar) : Prop :=
nullable_set_sound nu g /\ nullable_set_complete nu g.

Inductive first_sym (g : grammar) :
  lookahead -> symbol -> Prop :=
| FirstT : forall y,
    first_sym g (LA y) (T y)
| FirstNT : forall x gpre s gsuf la,
    In (x, gpre ++ s :: gsuf) g.(productions)
    -> nullable_gamma g gpre
    -> first_sym g la s
    -> first_sym g la (NT x).

Hint Constructors first_sym.

Inductive first_gamma (g : grammar) : lookahead -> list symbol -> Prop :=
| FirstGamma : forall gpre la s gsuf,
    nullable_gamma g gpre
    -> first_sym g la s
    -> first_gamma g la (gpre ++ s :: gsuf).

Hint Constructors first_gamma.

Definition first_map := NtMap.t LaSet.t.

Definition first_map_sound (fi : first_map) (g : grammar) : Prop :=
  forall x xFirst la,
    NtMap.find x fi = Some xFirst
    -> LaSet.In la xFirst
    -> first_sym g la (NT x).

(* We want a symbol in the first_sym hypothesis
   instead of an (NT x) so that induction is stronger *)
Definition first_map_complete (fi : first_map) (g : grammar) : Prop :=
  forall la sym x,
    first_sym g la sym
    -> sym = NT x
    -> exists xFirst,
      NtMap.find x fi = Some xFirst
      /\ LaSet.In la xFirst.

Definition first_map_for (fi : first_map) (g : grammar) : Prop :=
  first_map_sound fi g /\ first_map_complete fi g.

Inductive follow_sym (g : grammar) : lookahead -> symbol -> Prop :=
(*| FollowNullable : forall sym,
    nullable_sym g sym
    -> follow_sym g EOF sym *)
| FollowStart : forall x,
    x = g.(start)
    -> follow_sym g EOF (NT x)
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

Definition follow_map := NtMap.t LaSet.t.

Definition follow_map_sound (fo : follow_map) (g : grammar) : Prop :=
  forall x xFollow la,
    NtMap.find x fo = Some xFollow
    -> LaSet.In la xFollow
    -> follow_sym g la (NT x).

Definition follow_map_complete (fo : follow_map) (g : grammar) : Prop :=
  forall s x la,
    follow_sym g la s
    -> s = NT x
    -> exists xFollow,
      NtMap.find x fo = Some xFollow
      /\ LaSet.In la xFollow.

Definition follow_map_for (fo : follow_map) (g : grammar) : Prop :=
follow_map_sound fo g /\ follow_map_complete fo g.

Definition lookahead_for
           (la : lookahead)
           (x : nonterminal)
           (gamma : list symbol)
           (g : grammar) : Prop :=
  first_gamma g la gamma
  \/ (nullable_gamma g gamma
      /\ follow_sym g la (NT x)).

Definition lookahead_set_sound
           (laSet : LaSet.t)
           (x     : nonterminal)
           (gamma : list symbol)
           (g     : grammar) : Prop :=
  forall la, LaSet.In la laSet -> lookahead_for la x gamma g.

Definition lookahead_set_complete
           (laSet : LaSet.t)
           (x     : nonterminal)
           (gamma : list symbol)
           (g     : grammar) : Prop :=
  forall la, lookahead_for la x gamma g -> LaSet.In la laSet.

Definition lookahead_set_for
           (laSet : LaSet.t)
           (x     : nonterminal)
           (gamma : list symbol)
           (g     : grammar) : Prop :=
  lookahead_set_sound laSet x gamma g /\ lookahead_set_complete laSet x gamma g.

Definition pt_sound (tbl : parse_table) (g : grammar) :=
  forall (x : nonterminal) (la : lookahead) (gamma : list symbol),
    pt_lookup x la tbl = Some gamma -> In (x, gamma) g.(productions) /\ lookahead_for la x gamma g.

Definition pt_complete (tbl : parse_table) (g : grammar) :=
  forall (x : nonterminal) (la : lookahead) (gamma : list symbol),
    In (x, gamma) g.(productions) -> lookahead_for la x gamma g -> pt_lookup x la tbl = Some gamma.

Definition parse_table_for (tbl : parse_table) (g : grammar) :=
  pt_sound tbl g /\ pt_complete tbl g.

