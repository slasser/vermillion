Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.

(* Deprecated *)
(*
Definition prod_la_pair := (production * LaSet.t)%type.
Definition p_l_pair_wf (g : grammar) (p : p_l_pair) :=
  match p with
  | ((x, gamma), laSet) => lookahead_set_for laSet x gamma g
  end.
Definition p_l_pairs_wf (ps : list p_l_pair) (g : grammar) :=
  Forall (p_l_pair_wf g) ps.
 *)

Inductive pairs_wf (g : grammar) :
  list production -> list LaSet.t -> Prop :=
| Pairs_wf_nil  : pairs_wf g [] []
| Pairs_wf_cons : forall p_tl l_tl laSet x gamma,
    pairs_wf g p_tl l_tl
    -> lookahead_set_for laSet x gamma g
    -> pairs_wf g ((x, gamma) :: p_tl) (laSet :: l_tl).

Definition empty_pt := NtMap.empty (LaMap.t (list symbol)).

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

Definition addEntries (p : p_l_pair) (o : option parse_table) :=
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

Definition tbl_correct_for_pl_pairs tbl ps g :=
  p_l_pairs_wf ps g
  /\ tbl_sound_for_pl_pairs tbl ps
  /\ tbl_complete_for_pl_pairs tbl ps.

Conjecture empty_or_not :
  forall tbl,
    tbl = empty_pt
    \/ exists x,
      NtMap.In x tbl.

Conjecture tbl_correct_for_pl_pairs_parse_table_for :
  forall ps tbl g,
    tbl_correct_for_pl_pairs tbl ps g <-> parse_table_for tbl g.
(*
Proof.
  induction ps.
  - intros tbl g.
    split.
    + (* prove tbl is empty *)
      intros Htcf.
      assert (tbl = empty_pt).
      { unfold empty_pt.
        unfold tbl_correct_for_pl_pairs in Htcf.
        destruct Htcf as [Hwf [Hts Htc]].
        unfold tbl_sound_for_pl_pairs in Hts.
        pose proof empty_or_not as H.
        destruct (H tbl); auto.
*)        
  
(*
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
*)

Definition mkParseTable (productions_with_la_sets : list p_l_pair) :=
  fold_right addEntries (Some empty_pt) productions_with_la_sets.

Lemma mkParseTable_correct : 
  forall (ps : list p_l_pair)
         (tbl : parse_table)
         (g : grammar),
    p_l_pairs_wf ps g
    -> mkParseTable ps = Some tbl
       <-> parse_table_for tbl g.
Proof.
  intros ps tbl g Hwf.
  split.
  - (* prove mkParseTable sound -- if it returns parse table tbl,
 tbl is a parse table for g *)
    intros Hmk.
    apply tbl_correct_for_pl_pairs_parse_table_for with
        (ps := ps).
    

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