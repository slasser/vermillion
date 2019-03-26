Require Import List.

Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.

Require Import ParseTable.
Require Import ParseTableGen.

Require Import Proofs.Lemmas.

Require Import Proofs.ParseTableGen.mkEntries_Correctness.

Import ListNotations.

Definition table_correct_wrt_entries (tbl : parse_table) (es : list table_entry) :=
  forall x gamma la,
    pt_lookup x la tbl = Some gamma <-> In (x, la, gamma) es.

Lemma invariant_iff_parse_table_for :
  forall (g : grammar) (es : list table_entry) (tbl : parse_table),
    entries_correct es g
    -> table_correct_wrt_entries tbl es
       <-> parse_table_for tbl g.
Proof.
  intros g es tbl Hwf.
  split.
  - intros Htc.
    unfold table_correct_wrt_entries in Htc.
    split.
    + unfold pt_sound.
      intros x la gamma Hlk.
      apply Hwf.
      apply Htc; auto.
    + unfold pt_complete.
      intros la x gamma Hin Hlf.
      apply Htc.
      apply Hwf; auto.
  - intros Hpt.
    destruct Hpt as [Hsou Hcom].
    unfold table_correct_wrt_entries.
    intros x gamma la.
    split.
    + intros Hlk.
      apply Hwf.
      apply Hsou; auto.
    + intros Hin.
      apply Hwf in Hin.
      destruct Hin as [Hin Hlf].
      apply Hcom; auto.
Qed.

(* tableFromEntries soundness *)

Lemma addEntry_outer_Some_inner_Some :
  forall p o tbl,
    addEntry p o = Some tbl
    -> exists tbl',
      o = Some tbl'.
Proof.
  intros p o tbl Hadd.
  destruct p as ((x, la), gamma).
  destruct o as [tbl' |] eqn:Ho.
  - exists tbl'; auto.
  - unfold addEntry in Hadd; inv Hadd.
Qed.

Lemma duplicate_preserves_invariant :
  forall tbl es x la gamma,
    table_correct_wrt_entries tbl es
    -> pt_lookup x la tbl = Some gamma
    -> table_correct_wrt_entries tbl ((x, la, gamma) :: es).
Proof.
  intros tbl es x la gamma Htc Hlk.
  unfold table_correct_wrt_entries.
  intros x' gamma' la'.
  split.
  - intros Hlk'.
    unfold table_correct_wrt_entries in Htc.
    apply Htc in Hlk'.
    right; auto.
  - intros Hin.
    inv Hin.
    + inv H; auto.
    + apply Htc; auto.
Qed.

Lemma lookup_add_or :
  forall x x' la la' gamma gamma' tbl,
    pt_lookup x' la' (pt_add x la gamma tbl) = Some gamma'
    -> (x = x' /\ la = la' /\ gamma = gamma')
       \/ pt_lookup x' la' tbl = Some gamma'.
Proof.
  intros x x' la la' gamma gamma' tbl Hlk.
  unfold pt_lookup in Hlk; unfold pt_add in Hlk.
  rewrite ParseTableFacts.add_o in Hlk.
  destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
  - inv e.
    inv Hlk.
    left; auto.
  - right; auto.
Qed.

Lemma new_entry_preserves_invariant :
  forall tbl es x la gamma,
    table_correct_wrt_entries tbl es
    -> pt_lookup x la tbl = None
    -> table_correct_wrt_entries (pt_add x la gamma tbl) ((x, la, gamma) :: es).
Proof.
  intros tbl es x la gamma Htc Hlk.
  unfold table_correct_wrt_entries.
  intros x' gamma' la'.
  split.
  - intros Hlk'.
    apply lookup_add_or in Hlk'.
    inv Hlk'.
    + destruct H as [Hx [Hla Hgamma]]; subst.
      left; auto.
    + apply Htc in H.
      right; auto.
  - intros Hin.
    inv Hin.
    + inv H.
      unfold pt_lookup.
      unfold pt_add.
      apply ParseTableFacts.add_eq_o; auto.
    + apply Htc in H.
      destruct (ParseTableFacts.eq_dec (x, la) (x', la')). 
      * inv e; congruence.
      * unfold pt_lookup.
        unfold pt_add.
        rewrite ParseTableFacts.add_neq_o; auto.
Qed.

Lemma addEntry_preserves_invariant :
  forall (p : table_entry)
         (ps : list table_entry)
         (tbl' tbl : parse_table),
    table_correct_wrt_entries tbl' ps
    -> addEntry p (Some tbl') = Some tbl
    -> table_correct_wrt_entries tbl (p :: ps).
Proof.
  intros ((x, la), gamma) es tbl' tbl Htc Hadd.
  unfold addEntry in Hadd.
  destruct (pt_lookup x la tbl') as [gamma' |] eqn:Hlk.
  - destruct (list_eq_dec symbol_eq_dec gamma gamma').
    + inv e.
      inv Hadd.
      apply duplicate_preserves_invariant; auto.
    + inv Hadd.
  - inv Hadd.
    apply new_entry_preserves_invariant; auto.
Qed.

Lemma empty_table_correct_wrt_empty_entries :
  table_correct_wrt_entries empty_table [].
Proof.
  unfold table_correct_wrt_entries.
  intros x gamma la.
  split.
  - intros Hlk.
    unfold pt_lookup in Hlk.
    rewrite ParseTableFacts.empty_o in Hlk; inv Hlk.
  - intros Hin; inv Hin.
Qed.

Lemma mkParseTable_sound_wrt_invariant :
  forall (es  : list table_entry)
         (tbl : parse_table),
    mkParseTable es = Some tbl
    -> table_correct_wrt_entries tbl es.
Proof.
  intros es.
  induction es as [| p ps]; intros tbl Hmk; simpl in *.
  - inv Hmk.
    apply empty_table_correct_wrt_empty_entries.
  - pose proof Hmk as Hmk'.
    apply addEntry_outer_Some_inner_Some in Hmk.
    destruct Hmk as [tbl' Hmk].
    rewrite Hmk in Hmk'.
    eapply addEntry_preserves_invariant; eauto.
Qed.

Lemma mkParseTable_sound :
  forall (es  : list table_entry)
         (g   : grammar)
         (tbl : parse_table),
    entries_correct es g
    -> mkParseTable es = Some tbl
    -> parse_table_for tbl g.
Proof.
  intros es g tbl Hwf Hmk.
  eapply invariant_iff_parse_table_for; eauto.
  apply mkParseTable_sound_wrt_invariant; auto.
Qed.

(* tableFromEntries completeness *)

Lemma table_correct_wrt_empty_entries_eq_empty_table :
  forall tbl,
    table_correct_wrt_entries tbl []
    -> ParseTable.Equal tbl empty_table.
Proof.
  intros tbl Htc.
  unfold ParseTable.Equal.
  intros (x, la).
  unfold table_correct_wrt_entries in Htc.
  destruct (pt_lookup x la tbl) as [gamma |] eqn:Hlk.
  - apply Htc in Hlk.
    inv Hlk.
  - rewrite ParseTableFacts.empty_o; auto.
Qed.

Lemma invariant_cons_duplicate_invariant_tail :
  forall tbl x gamma la ps,
    table_correct_wrt_entries tbl ((x, la, gamma) :: ps)
    -> In (x, la, gamma) ps
    -> table_correct_wrt_entries tbl ps.
Proof.
  intros tbl x gamma la es Htc Hin.
  unfold table_correct_wrt_entries in Htc.
  unfold table_correct_wrt_entries.
  intros x' gamma' la'.
  split.
  - intros Hlk.
    apply Htc in Hlk.
    inv Hlk; auto.
    inv H; auto.
  - intros Hin'.
    apply Htc.
    right; auto.
Qed.

Lemma eq_pairs_eq_gammas :
  forall tbl es x gamma gamma' la,
    table_correct_wrt_entries tbl es
    -> In (x, la, gamma) es
    -> In (x, la, gamma') es
    -> gamma = gamma'.
Proof.
  intros tbl es x gamma gamma' la Htc Hin Hin'.
  apply Htc in Hin.
  apply Htc in Hin'.
  congruence.
Qed.
  
Lemma invariant_cons_eq_gammas :
  forall tbl x gamma la es,
    table_correct_wrt_entries tbl ((x, la, gamma) :: es)
    -> forall gamma',
      In (x, la, gamma') es
      -> gamma = gamma'.
Proof.
  intros tbl x gamma la es Htc gamma' Hin.
  unfold table_correct_wrt_entries in Htc.
  destruct (list_eq_dec symbol_eq_dec gamma gamma'); auto.
  assert (H : In (x, la, gamma) ((x, la, gamma) :: es)).
  { left; auto. }
  assert (H' : In (x, la, gamma') ((x, la, gamma) :: es)).
  { right; auto. }
  apply Htc in H.
  apply Htc in H'.
  congruence.
Qed.
  
(* BUG : originally had this as add instead of remove *)
Lemma invariant_cons_new_entry_invariant_remove :
  forall tbl x gamma la ps,
    table_correct_wrt_entries tbl ((x, la, gamma) :: ps)
    -> ~In (x, la, gamma) ps
    -> table_correct_wrt_entries (ParseTable.remove (x, la) tbl) ps.
Proof.
  intros tbl x gamma la es Htc Hin.
  unfold table_correct_wrt_entries.
  intros x' gamma' la'.
  split.
  - intros Hlk.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
    + inv e.
      unfold pt_lookup in Hlk.
      rewrite ParseTableFacts.remove_eq_o in Hlk; inv Hlk; auto.
    + unfold pt_lookup in Hlk.
      rewrite ParseTableFacts.remove_neq_o in Hlk; auto.
      unfold table_correct_wrt_entries in Htc.
      apply Htc in Hlk.
      inv Hlk; congruence.
  - intros Hin'.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
    + inv e.
      destruct (list_eq_dec symbol_eq_dec gamma gamma').
      * subst.
        congruence.
      * eapply invariant_cons_eq_gammas with (gamma' := gamma') in Htc; auto.
        congruence.
    + unfold pt_lookup.
      rewrite ParseTableFacts.remove_neq_o; auto.
      apply Htc.
      right; auto.
Qed.
    
Lemma correct_post_table_implies_correct_pre_table :
  forall tbl x gamma la es,
    table_correct_wrt_entries tbl ((x, la, gamma) :: es)
    -> exists tbl',
      table_correct_wrt_entries tbl' es.
Proof.
  intros tbl x gamma la es Htc.
  destruct (in_dec table_entry_dec (x, la, gamma) es).
  - (* duplicate *)
    exists tbl.
    eapply invariant_cons_duplicate_invariant_tail; eauto.
  - exists (ParseTable.remove (x, la) tbl).
    eapply invariant_cons_new_entry_invariant_remove; eauto.
Qed.

Lemma invariant_tables_eq :
  forall tbl tbl' ps,
    table_correct_wrt_entries tbl ps
    -> table_correct_wrt_entries tbl' ps
    -> ParseTable.Equal tbl tbl'.
Proof.
  intros tbl tbl' es Htc Htc'.
  unfold ParseTable.Equal.
  intros (x, la).
  destruct (ParseTable.find (x, la) tbl) as [gamma |] eqn:Hf.
  - destruct (ParseTable.find (x, la) tbl') as [gamma' |] eqn:Hf'.
    + apply Htc in Hf.
      apply Htc' in Hf'.
      eapply eq_pairs_eq_gammas with
          (gamma := gamma)
          (gamma' := gamma') in Htc; eauto.
      congruence.
    + apply Htc in Hf.
      apply Htc' in Hf.
      unfold pt_lookup in Hf; congruence.
  - destruct (ParseTable.find (x, la) tbl') as [gamma' |] eqn:Hf'.
    + apply Htc' in Hf'.
      apply Htc in Hf'.
      unfold pt_lookup in Hf'; congruence.
    + auto.
Qed.

Lemma invariant_not_in_add :
  forall tbl tbl' es x gamma la,
    table_correct_wrt_entries tbl es
    -> table_correct_wrt_entries tbl' ((x, la, gamma) :: es)
    -> ~In (x, la, gamma) es
    -> table_correct_wrt_entries (pt_add x la gamma tbl) ((x, la, gamma) :: es).
Proof.
  intros tbl tbl' es x gamma la Htc Htc' Hin.
  intros x' gamma' la'.
  split.
  - intros Hlk.
    unfold pt_lookup, pt_add in Hlk.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
    + inv e.
      rewrite ParseTableFacts.add_eq_o in Hlk; auto.
      inv Hlk.
      left; auto.
    + rewrite ParseTableFacts.add_neq_o in Hlk; auto.
      apply Htc in Hlk.
      right; auto.
  - intros Hin'.
    unfold pt_lookup, pt_add.
    inv Hin'.
    + inv H.
      rewrite ParseTableFacts.add_eq_o; auto.
    + destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
      * inv e.
        apply invariant_cons_eq_gammas with (gamma' := gamma') in Htc'; auto.
        congruence.
      * rewrite ParseTableFacts.add_neq_o; auto.
        apply Htc; auto.
Qed.

Lemma add_preserves_equal :
  forall tbl tbl' x la gamma,
    ParseTable.Equal tbl tbl'
    -> ParseTable.Equal (pt_add x la gamma tbl) (pt_add x la gamma tbl').
Proof.
  intros tbl tbl' x la gamma Heq.
  unfold ParseTable.Equal.
  intros (x', la').
  unfold pt_add.
  destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
  - inv e.
    repeat rewrite ParseTableFacts.add_eq_o; auto.
  - repeat rewrite ParseTableFacts.add_neq_o; auto.
Qed.

Lemma addEntry_duplicate_doesn't_change_table :
  forall tbl es x gamma la,
    table_correct_wrt_entries tbl es
    -> In (x, la, gamma) es
    -> addEntry (x, la, gamma) (Some tbl) = Some tbl.
Proof.
  intros tbl es x gamma la Htc Hin.
  unfold addEntry.
  apply Htc in Hin.
  rewrite Hin.
  (* lemma? *)
  destruct (list_eq_dec symbol_eq_dec gamma gamma); [auto | congruence].
Qed.

Lemma equal_preserves_invariant :
  forall tbl tbl' ps,
    table_correct_wrt_entries tbl ps
    -> ParseTable.Equal tbl tbl'
    -> table_correct_wrt_entries tbl' ps.
Proof.
  intros tbl tbl' es Htc Heq.
  auto.
  unfold table_correct_wrt_entries in Htc.
  unfold pt_lookup in Htc.
  intros x gamma la.
  split; [intros Hlk | intros Hin].
  - apply Htc.
    unfold ParseTable.Equal in Heq.
    rewrite Heq; auto.
  - unfold pt_lookup. 
    rewrite <- Heq.
    apply Htc; auto.
Qed.

Lemma addEntry_new_entry_pt_add :
  forall tbl tbl' es x gamma la,
    table_correct_wrt_entries tbl es
    -> table_correct_wrt_entries tbl' ((x, la, gamma) :: es)
    -> ~ In (x, la, gamma) es
    -> addEntry (x, la, gamma) (Some tbl) = Some (pt_add x la gamma tbl).
Proof.
  intros tbl tbl' es x gamma la Htc Htc' Hin.
  unfold addEntry.
  destruct (pt_lookup x la tbl) as [gamma' |] eqn:Hlk.
  - apply Htc in Hlk. 
    apply invariant_cons_eq_gammas with (gamma' := gamma') in Htc'; auto.
    congruence.
  - auto.
Qed.

Lemma mkParseTable_complete_wrt_invariant :
  forall es tbl,
    table_correct_wrt_entries tbl es
    -> exists tbl',
      ParseTable.Equal tbl tbl'
      /\ mkParseTable es = Some tbl'.
Proof.
  intros es.
  induction es as [| ((x, la), gamma) es]; intros post_tbl Htc.
  - apply table_correct_wrt_empty_entries_eq_empty_table in Htc.
    exists empty_table; auto.
  - pose proof Htc as Htc'.
    apply correct_post_table_implies_correct_pre_table in Htc.
    destruct Htc as [pre_tbl Htc].
    pose proof Htc as Htc''.
    apply IHes in Htc.
    destruct Htc as [pre_tbl' [Hpreq Hpremk]].
    destruct (in_dec table_entry_dec (x, la, gamma) es).
    + exists pre_tbl'; split.
      * apply invariant_cons_duplicate_invariant_tail in Htc'; auto.
        apply ParseTableFacts.Equal_trans with (m' := pre_tbl); auto.
        eapply invariant_tables_eq; eauto.
      * simpl.
        rewrite Hpremk.
        eapply addEntry_duplicate_doesn't_change_table; eauto.
        eapply equal_preserves_invariant; eauto.
    + exists (pt_add x la gamma pre_tbl'); split.
      * eapply invariant_not_in_add in Htc''; eauto.
        apply add_preserves_equal with 
            (x := x)
            (la := la)
            (gamma := gamma) in Hpreq; eauto.
        apply invariant_tables_eq with (tbl := post_tbl) in Htc''; auto.
        apply ParseTableFacts.Equal_trans with (m' := pt_add x la gamma pre_tbl); auto.
      * simpl.
        rewrite Hpremk.
        eapply addEntry_new_entry_pt_add; eauto.
        eapply equal_preserves_invariant; eauto.
Qed.

Lemma mkParseTable_complete :
  forall (es  : list table_entry)
         (g   : grammar)
         (tbl : parse_table),
    entries_correct es g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ mkParseTable es = Some tbl'.
Proof.
  intros es g tbl Hwf Hpt.
  eapply mkParseTable_complete_wrt_invariant.
  eapply invariant_iff_parse_table_for; eauto.
Qed.
  
