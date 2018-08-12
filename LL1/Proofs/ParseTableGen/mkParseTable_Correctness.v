Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Require Import LL1.Proofs.Lemmas.

Require Import LL1.Proofs.ParseTableGen.mkParseTableEntries_Correctness.
Import ListNotations.

Definition tbl_correct_wrt_pairs (tbl : parse_table) (ps : list pt_entry) :=
  forall x gamma la,
    pt_lookup x la tbl = Some gamma <-> In (x, la, gamma) ps.

Lemma invariant_iff_parse_table_for :
  forall (g : grammar) (ps : list pt_entry) (tbl : parse_table),
    pt_entries_correct ps g
    -> tbl_correct_wrt_pairs tbl ps
       <-> parse_table_for tbl g.
Proof.
  intros g ps tbl Hwf.
  split.
  - intros Htc.
    unfold tbl_correct_wrt_pairs in Htc.
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
    unfold tbl_correct_wrt_pairs.
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

(* mkParseTable soundness *)

Lemma addEntry_preserves_Some :
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
  forall tbl ps x la gamma,
    tbl_correct_wrt_pairs tbl ps
    -> pt_lookup x la tbl = Some gamma
    -> tbl_correct_wrt_pairs tbl ((x, la, gamma) :: ps).
Proof.
  intros tbl ps x la gamma Htc Hlk.
  unfold tbl_correct_wrt_pairs.
  intros x' gamma' la'.
  split.
  - intros Hlk'.
    unfold tbl_correct_wrt_pairs in Htc.
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
  forall tbl ps x la gamma,
    tbl_correct_wrt_pairs tbl ps
    -> pt_lookup x la tbl = None
    -> tbl_correct_wrt_pairs (pt_add x la gamma tbl) ((x, la, gamma) :: ps).
Proof.
  intros tbl ps x la gamma Htc Hlk.
  unfold tbl_correct_wrt_pairs.
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
  forall (p : pt_entry)
         (ps : list pt_entry)
         (tbl' tbl : parse_table),
    tbl_correct_wrt_pairs tbl' ps
    -> addEntry p (Some tbl') = Some tbl
    -> tbl_correct_wrt_pairs tbl (p :: ps).
Proof.
  intros ((x, la), gamma) ps tbl' tbl Htc Hadd.
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

Lemma empty_table_correct_wrt_empty_pairs :
  tbl_correct_wrt_pairs empty_pt [].
Proof.
  unfold tbl_correct_wrt_pairs.
  intros x gamma la.
  split.
  - intros Hlk.
    unfold pt_lookup in Hlk.
    rewrite ParseTableFacts.empty_o in Hlk; inv Hlk.
  - intros Hin; inv Hin.
Qed.

Lemma mkParseTable_sound_wrt_invariant :
  forall (ps  : list pt_entry)
         (tbl : parse_table),
    mkParseTable ps = Some tbl
    -> tbl_correct_wrt_pairs tbl ps.
Proof.
  intros ps.
  induction ps as [| p ps]; intros tbl Hmk; simpl in *.
  - inv Hmk.
    apply empty_table_correct_wrt_empty_pairs.
  - pose proof Hmk as Hmk'.
    apply addEntry_preserves_Some in Hmk.
    destruct Hmk as [tbl' Hmk].
    rewrite Hmk in Hmk'.
    eapply addEntry_preserves_invariant; eauto.
Qed.

Lemma mkParseTable_sound :
  forall (ps  : list pt_entry)
         (g   : grammar)
         (tbl : parse_table),
    pt_entries_correct ps g
    -> mkParseTable ps = Some tbl
    -> parse_table_for tbl g.
Proof.
  intros ps g tbl Hwf Hmk.
  eapply invariant_iff_parse_table_for; eauto.
  apply mkParseTable_sound_wrt_invariant; auto.
Qed.

(* mkParseTable completeness *)

Lemma table_correct_wrt_empty_pairs_eq_empty_table :
  forall tbl,
    tbl_correct_wrt_pairs tbl []
    -> ParseTable.Equal tbl empty_pt.
Proof.
  intros tbl Htc.
  unfold ParseTable.Equal.
  intros (x, la).
  unfold tbl_correct_wrt_pairs in Htc.
  destruct (pt_lookup x la tbl) as [gamma |] eqn:Hlk.
  - apply Htc in Hlk.
    inv Hlk.
  - rewrite ParseTableFacts.empty_o; auto.
Qed.

Lemma invariant_cons_duplicate_invariant_tail :
  forall tbl x gamma la ps,
    tbl_correct_wrt_pairs tbl ((x, la, gamma) :: ps)
    -> In (x, la, gamma) ps
    -> tbl_correct_wrt_pairs tbl ps.
Proof.
  intros tbl x gamma la ps Htc Hin.
  unfold tbl_correct_wrt_pairs in Htc.
  unfold tbl_correct_wrt_pairs.
  intros x' gamma' la'.
  split.
  - (* prove soundness direction *)
    intros Hlk.
    apply Htc in Hlk.
    inv Hlk; auto.
    inv H; auto.
  - (* completeness direction *)
    intros Hin'.
    apply Htc.
    right; auto.
Qed.

Lemma eq_pairs_eq_gammas :
  forall tbl ps x gamma gamma' la,
    tbl_correct_wrt_pairs tbl ps
    -> In (x, la, gamma) ps
    -> In (x, la, gamma') ps
    -> gamma = gamma'.
Proof.
  intros tbl ps x gamma gamma' la Htc Hin Hin'.
  apply Htc in Hin.
  apply Htc in Hin'.
  congruence.
Qed.
  
Lemma invariant_cons_eq_gammas :
  forall tbl x gamma la ps,
    tbl_correct_wrt_pairs tbl ((x, la, gamma) :: ps)
    -> forall gamma',
      In (x, la, gamma') ps
      -> gamma = gamma'.
Proof.
  intros tbl x gamma la ps Htc gamma' Hin.
  unfold tbl_correct_wrt_pairs in Htc.
  destruct (list_eq_dec symbol_eq_dec gamma gamma'); auto.
  assert (H : In (x, la, gamma) ((x, la, gamma) :: ps)).
  { left; auto. }
  assert (H' : In (x, la, gamma') ((x, la, gamma) :: ps)).
  { right; auto. }
  apply Htc in H.
  apply Htc in H'.
  congruence.
Qed.
  
(* BUG : originally had this as add instead of remove *)
Lemma invariant_cons_new_entry_invariant_remove :
  forall tbl x gamma la ps,
    tbl_correct_wrt_pairs tbl ((x, la, gamma) :: ps)
    -> ~In (x, la, gamma) ps
    -> tbl_correct_wrt_pairs (ParseTable.remove (x, la) tbl) ps.
Proof.
  intros tbl x gamma la ps Htc Hin.
  unfold tbl_correct_wrt_pairs.
  intros x' gamma' la'.
  split.
  - intros Hlk.
    destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
    + inv e.
      unfold pt_lookup in Hlk.
      rewrite ParseTableFacts.remove_eq_o in Hlk; inv Hlk; auto.
    + unfold pt_lookup in Hlk.
      rewrite ParseTableFacts.remove_neq_o in Hlk; auto.
      unfold tbl_correct_wrt_pairs in Htc.
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
  forall tbl x gamma la ps,
    tbl_correct_wrt_pairs tbl ((x, la, gamma) :: ps)
    -> exists tbl',
      tbl_correct_wrt_pairs tbl' ps.
Proof.
  intros tbl x gamma la ps Htc.
  destruct (in_dec pt_entry_dec (x, la, gamma) ps).
  - (* duplicate *)
    exists tbl.
    eapply invariant_cons_duplicate_invariant_tail; eauto.
  - exists (ParseTable.remove (x, la) tbl).
    eapply invariant_cons_new_entry_invariant_remove; eauto.
Qed.

Lemma invariant_tables_eq :
  forall tbl tbl' ps,
    tbl_correct_wrt_pairs tbl ps
    -> tbl_correct_wrt_pairs tbl' ps
    -> ParseTable.Equal tbl tbl'.
Proof.
  intros tbl tbl' ps Htc Htc'.
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
  forall tbl tbl' ps x gamma la,
    tbl_correct_wrt_pairs tbl ps
    -> tbl_correct_wrt_pairs tbl' ((x, la, gamma) :: ps)
    -> ~In (x, la, gamma) ps
    -> tbl_correct_wrt_pairs (pt_add x la gamma tbl) ((x, la, gamma) :: ps).
Proof.
  intros tbl tbl' ps x gamma la Htc Htc' Hin.
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
  forall tbl ps x gamma la,
    tbl_correct_wrt_pairs tbl ps
    -> In (x, la, gamma) ps
    -> addEntry (x, la, gamma) (Some tbl) = Some tbl.
Proof.
  intros tbl ps x gamma la Htc Hin.
  unfold addEntry.
  apply Htc in Hin.
  rewrite Hin.
  (* lemma? *)
  destruct (list_eq_dec symbol_eq_dec gamma gamma); [auto | congruence].
Qed.

Lemma equal_preserves_invariant :
  forall tbl tbl' ps,
    tbl_correct_wrt_pairs tbl ps
    -> ParseTable.Equal tbl tbl'
    -> tbl_correct_wrt_pairs tbl' ps.
Proof.
  intros tbl tbl' ps Htc Heq.
  auto.
  unfold tbl_correct_wrt_pairs in Htc.
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
  forall tbl tbl' ps x gamma la,
    tbl_correct_wrt_pairs tbl ps
    -> tbl_correct_wrt_pairs tbl' ((x, la, gamma) :: ps)
    -> ~ In (x, la, gamma) ps
    -> addEntry (x, la, gamma) (Some tbl) = Some (pt_add x la gamma tbl).
Proof.
  intros tbl tbl' ps x gamma la Htc Htc' Hin.
  unfold addEntry.
  destruct (pt_lookup x la tbl) as [gamma' |] eqn:Hlk.
  - apply Htc in Hlk. 
    apply invariant_cons_eq_gammas with (gamma' := gamma') in Htc'; auto.
    congruence.
  - auto.
Qed.

Lemma mkParseTable_complete_wrt_invariant :
  forall ps tbl,
    tbl_correct_wrt_pairs tbl ps
    -> exists tbl',
      ParseTable.Equal tbl tbl'
      /\ mkParseTable ps = Some tbl'.
Proof.
  intros ps.
  induction ps as [| ((x, la), gamma) ps]; intros post_tbl Htc.
  - apply table_correct_wrt_empty_pairs_eq_empty_table in Htc.
    exists empty_pt; auto.
  - pose proof Htc as Htc'.
    apply correct_post_table_implies_correct_pre_table in Htc.
    destruct Htc as [pre_tbl Htc].
    pose proof Htc as Htc''.
    apply IHps in Htc.
    destruct Htc as [pre_tbl' [Hpreq Hpremk]].
    destruct (in_dec pt_entry_dec (x, la, gamma) ps).
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
  forall (ps  : list pt_entry)
         (g   : grammar)
         (tbl : parse_table),
    pt_entries_correct ps g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ mkParseTable ps = Some tbl'.
Proof.
  intros ps g tbl Hwf Hpt.
  eapply mkParseTable_complete_wrt_invariant.
  eapply invariant_iff_parse_table_for; eauto.
Qed.
  
