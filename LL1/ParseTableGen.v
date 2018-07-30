Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.

Definition pl_pair := (production * LaSet.t)%type.

Definition pl_pair_wf (g : grammar) (p : pl_pair) :=
  match p with
  | ((x, gamma), laSet) => lookahead_set_for laSet x gamma g
  end.

Definition pl_pairs_wf (g : grammar) (ps : list pl_pair) :=
  Forall (pl_pair_wf g) ps.

Definition singletonLaMap la gamma :=
  LaMap.add la gamma (LaMap.empty (list symbol)).
  
Definition addEntry (x : nonterminal) (la : lookahead) (gamma : list symbol) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl => 
    match NtMap.find x tbl with
    | None => Some (NtMap.add x (singletonLaMap la gamma) tbl)
    | Some m =>
      match LaMap.find la m with
      | None => Some (NtMap.add x (LaMap.add la gamma m) tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None
      end
    end
  end.

Definition addEntries (p : pl_pair) (o : option parse_table) :=
  match p with
  | ((x, gamma), laSet) =>
    fold_right (fun la o => addEntry x la gamma o) o (LaSet.elements laSet)
  end.

Definition tbl_sound_for_pl_pairs tbl pls :=
  forall x la gamma,
    pt_lookup x la tbl = Some gamma
    -> exists laSet,
      In ((x, gamma), laSet) pls
      /\ LaSet.In la laSet.

Definition tbl_complete_for_pl_pairs tbl pls :=
  forall x gamma la laSet,
    In ((x, gamma), laSet) pls
    -> LaSet.In la laSet
    -> pt_lookup x la tbl = Some gamma.

Definition tbl_correct_for_pl_pairs tbl pls :=
  tbl_sound_for_pl_pairs tbl pls /\ tbl_complete_for_pl_pairs tbl pls.

Lemma addEntries_preserves_invariant :
  forall laSet g p ps x gamma tbl tbl',
    p = ((x, gamma), laSet)
    -> pl_pairs_wf g (p :: ps)
    -> tbl_correct_for_pl_pairs tbl ps 
    -> addEntries p (Some tbl) = Some tbl'
    -> tbl_correct_for_pl_pairs tbl' (p :: ps).
Proof.
  intros laSet.
  remember (LaSet.elements laSet) as elts.
  generalize dependent laSet.
  induction elts; intros laSet Helts g p ps x gamma tbl tbl' Heq Htc Had.
  - subst.
    admit.
  - unfold pl_pairs_wf in Htc. 
    inv Htc.
subst.
    unfold addEntries in Had. 
    rewrite <- Helts in Had.
    simpl in Had.
    destruct (fold_right (fun la o => addEntry x la gamma o) (Some tbl) elts) eqn:Htl.
    + unfold addEntry in Had.
      destruct (NtMap.find x p) eqn:Hnf.
      * destruct (LaMap.find a t) eqn:Hlf.
        -- destruct (list_eq_dec symbol_eq_dec gamma l).
           ++ inv Had.
              eapply IHelts; eauto.


Definition empty_pt := NtMap.empty (LaMap.t (list symbol)).

Definition mkParseTable (productions_with_la_sets : list (production * LaSet.t)) :=
  fold_right addProductionEntries (Some empty_pt) productions_with_la_sets.

(*
Lemma mkParseTable_correct : 
  forall (productions_and_la_sets : list (production * LaSet.t))
         (tbl : parse_table),
    -> mkParseTable productions_and_la_sets = Some tbl
    -> forall (start : nonterminal)
              (productions : list production),
        productions = map fst productions_and_la_sets
        (* productions_and_la_sets is well-formed *)
        -> 
       <-> parse_table_for tbl g.
Proof.
  intros; split.
  - revert g tbl H.
    induction productions_and_la_sets.
    + (* empty list of productions and lookahead sets --
         the grammar's productions must be empty, so mkParseTable should return 
         an empty table *)
      intros g tbl Hprods Hmk.
      simpl in *.
      inv Hmk.
      unfold parse_table_for; split.
      * unfold pt_minimal; intros x la gamma laMap Hnf Hlf.
        exfalso; eapply NtMapFacts.empty_in_iff.
        apply ntmap_find_in in Hnf; eauto.
      * unfold pt_complete; intros x la gamma Hlf.
        exfalso.
        unfold lookahead_for in Hlf.
        destruct Hlf as [Hin _].
        rewrite Hprods in Hin; inv Hin.
    + intros g tbl Hprods Hmk.
      destruct a as [[x gamma] laSet].
*)