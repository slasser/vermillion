Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Require Import LL1.Proofs.Lemmas.

Import ListNotations.

Definition pt_entries_correct ps g :=
  forall x la gamma,
    In (x, la, gamma) ps
    <-> In (x, gamma) g.(productions)
        /\ lookahead_for la x gamma g.

(* invariant relating a list of entries to a list of productions *)
Definition entries_correct_wrt_productions es ps g :=
  forall x la gamma,
    In (x, la, gamma) es <-> In (x, gamma) ps /\ lookahead_for la x gamma g.

Lemma invariant_iff_pt_entries_correct :
  forall es g,
    entries_correct_wrt_productions es (productions g) g <-> pt_entries_correct es g.
Proof.
  intros es g.
  split; [intros Hinv | intros Hspec].
  - unfold entries_correct_wrt_productions, pt_entries_correct in *.
    intros x la gamma.
    split; [intros Hin | intros [Hin Hlf]].
    + apply Hinv in Hin.
      destruct Hin; auto.
    + apply Hinv; auto.
  - unfold pt_entries_correct, entries_correct_wrt_productions in *.
    intros x la gamma.
    split; [intros Hin | intros [Hin Hlf]].
    + split.
      * apply Hspec in Hin.
        destruct Hin; auto.
      * apply Hspec; auto.
    + apply Hspec; auto.
Qed.

Lemma empty_entries_correct_wrt_empty_productions :
  forall g,
    entries_correct_wrt_productions [] [] g.
Proof.
  intros g.
  split; [intros Hin | intros [Hin _]]; inv Hin.
Qed.

Lemma fromLookaheadList_preserves_prod :
  forall x x' la gamma gamma' las,
    In (x, la, gamma) (fromLookaheadList x' gamma' las)
    -> (x, gamma) = (x', gamma').
Proof.
  intros x x' la gamma gamma' las Hin.
  induction las as [| la' las]; simpl in *.
  - inv Hin.
  - inv Hin.
    + inv H; auto.
    + apply IHlas; auto.
Qed.

Lemma mkEntriesForProd_preserves_prod :
  forall x la gamma nu fi fo p,
    In (x, la, gamma) (mkEntriesForProd nu fi fo p)
    -> (x, gamma) = p.
Proof.
  intros x la gamma nu fi fo p Hin.
  destruct p as (x', gamma').
  unfold mkEntriesForProd in Hin.
  apply in_app_or in Hin.
  inv Hin; eapply fromLookaheadList_preserves_prod; eauto.
Qed.

Lemma first_gamma_tail_first_gamma_cons :
  forall g la x syms,
    nullable_sym g (NT x)
    -> first_gamma g la syms
    -> first_gamma g la (NT x :: syms).
Proof.
  intros g la x syms Hnu Hfi.
  induction Hfi.
  apply FirstGamma with (gpre := NT x :: gpre); auto.
Qed.

Lemma in_elements_iff_in_set :
  forall la s,
    In la (LaSet.elements s) <-> LaSet.In la s.
Proof.
  intros la s.
  split; intros Hin.
  - apply LaSetFacts.elements_iff.
    apply SetoidList.In_InA; auto.
  - rewrite LaSetFacts.elements_iff in Hin.
    apply SetoidList.InA_alt in Hin.
    destruct Hin as [la' [Heq Hin]].
    subst; auto.
Qed.

Lemma first_gamma_terminal_head :
  forall g la y syms,
    first_gamma g la (T y :: syms)
    -> la = LA y.
Proof.
  intros g la y syms Hfi.
  pose proof Hfi as Hfi'.
  inv Hfi.
  destruct gpre; simpl in *.
  - inv H.
    inv H2; auto.
  - inv H.
    exfalso.
    eapply gamma_with_terminal_not_nullable with
        (gpre := nil)
        (y := y)
        (gsuf := gpre); eauto.
Qed.

Lemma first_gamma_head_or_tail :
  forall g la sym syms,
    first_gamma g la (sym :: syms)
    -> first_sym g la sym
       \/ (nullable_sym g sym
           /\ first_gamma g la syms).
Proof.
  intros g la sym syms Hfi.
  pose proof Hfi as Hfi'.
  inv Hfi.
  destruct gpre; simpl in *.
  - inv H; auto.
  - inv H.
    right.
    split.
    + inv H0; auto.
    + inv H0.
      apply FirstGamma with (gpre := gpre); auto.
Qed.

Lemma firstGamma_sound :
  forall g la nu fi gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> In la (firstGamma gamma nu fi)
    -> first_gamma g la gamma.
Proof.
  intros g la nu fi gamma Hns Hfm Hin.
  induction gamma as [| sym syms]; simpl in *.
  - inv Hin.
  - destruct sym as [y | x].
    + inv Hin.
      * apply FirstGamma with (gpre := nil); auto.
      * inv H.
    + destruct (NtSet.mem x nu) eqn:Hmem.
      * destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
        -- apply in_app_or in Hin.
           inv Hin.
           ++ destruct Hfm as [Hsou Hcom].
              unfold first_map_sound in Hsou.
              apply Hsou with (la := la) in Hfind.
              ** apply FirstGamma with (gpre := nil); auto.
              ** apply in_elements_iff_in_set; auto.
           ++ apply first_gamma_tail_first_gamma_cons; auto.
              destruct Hns as [Hsou Hcom].
              apply Hsou.
              apply NtSet.mem_spec; auto.
        -- simpl in *.
           apply first_gamma_tail_first_gamma_cons; auto.
           destruct Hns as [Hsou Hcom].
           apply Hsou.
           apply NtSet.mem_spec; auto.
      * destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
        -- destruct Hfm as [Hsou com].
           eapply Hsou in Hfind.
           apply FirstGamma with (gpre := nil); auto.
           apply Hfind.
           apply in_elements_iff_in_set; auto.
        -- inv Hin.
Qed.

(* There's probably a way to shorten this *)
Lemma firstGamma_complete :
    forall g la nu fi gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> first_gamma g la gamma
    -> In la (firstGamma gamma nu fi).
Proof.
  intros g la nu fi gamma Hnu Hfm Hfg.
  induction gamma as [| sym syms].
  - simpl in *.
    inv Hfg. (* LEMMA *)
    symmetry in H.
    apply app_cons_not_nil in H; inv H.
  - destruct sym as [y | x]; simpl in *.
    + apply first_gamma_terminal_head in Hfg; auto.
    + destruct (NtSet.mem x nu) eqn:Hmem.
      * (* x is in the nullable set, so we know it's nullable *)
        destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
        -- apply in_or_app.
           apply first_gamma_head_or_tail in Hfg.
           inv Hfg.
           ++ destruct Hfm as [Hsou Hcom].
              eapply Hcom in H.
              destruct H as [fiSet' [Hnf Hlin]]; auto.
              left.
              assert (fiSet = fiSet') by congruence; subst.
             apply in_elements_iff_in_set; auto.
           ++ destruct H.
              right; auto.
        -- simpl.
           apply IHsyms.
           apply first_gamma_head_or_tail in Hfg.
           inv Hfg.
           ++ destruct Hfm as [Hsou Hcom].
              eapply Hcom in H.
              destruct H as [fiSet' [Hnf Hli]]; auto.
              congruence.
           ++ destruct H; auto.
      * destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
        -- apply first_gamma_head_or_tail in Hfg.
           inv Hfg.
           ++ destruct Hfm as [Hsou Hcom].
              eapply Hcom in H.
              destruct H as [fiSet' [Hnf Hli]]; auto.
              assert (fiSet = fiSet') by congruence; subst.
              apply in_elements_iff_in_set; auto.
           ++ destruct H.
              destruct Hnu as [Hsou Hcom].
              apply Hcom in H.
              rewrite <- NtSet.mem_spec in H.
              congruence.
        -- apply first_gamma_head_or_tail in Hfg.
           inv Hfg.
           ++ destruct Hfm as [Hsou Hcom].
              eapply Hcom in H.
              destruct H as [fiSet [Hnf Hli]]; auto.
              congruence.
           ++ destruct H.
              destruct Hnu as [Hsou Hcom].
              apply Hcom in H.
              rewrite <- NtSet.mem_spec in H.
              congruence.
Qed.

Lemma nullableGamma_correct :
  forall g nu gamma,
    nullable_set_for nu g
    -> nullableGamma gamma nu = true
       <-> nullable_gamma g gamma.
Proof.
  intros g nu gamma Hns.
  split; [intros Hf | intros Hr].
  - induction gamma as [| sym syms]; simpl in *; auto.
    + destruct sym as [y | x].
      * inv Hf.
      * destruct (NtSet.mem x nu) eqn:Hmem.
        -- constructor; auto.
           destruct Hns as [Hsou Hcom].
           apply Hsou.
           rewrite <- NtSet.mem_spec; auto.
        -- inv Hf.
  - induction gamma as [| sym syms]; simpl in *; auto.
    destruct sym as [y | x].
    + exfalso.
      eapply gamma_with_terminal_not_nullable with (gpre := nil); eauto.
    + inv Hr.
      destruct Hns as [Hsou Hcom].
      apply Hcom in H1.
      rewrite <- NtSet.mem_spec in H1.
      rewrite H1; auto.
Qed.
      
Lemma followLookahead_sound :
  forall g la nu fo x gamma,
    nullable_set_for nu g
    -> follow_map_for fo g
    -> In la (followLookahead x gamma nu fo)
    -> nullable_gamma g gamma /\ follow_sym g la (NT x).
Proof.
  intros g la nu fo x gamma Hns Hfm Hin.
  unfold followLookahead in Hin.
  destruct (nullableGamma gamma nu) eqn:Hng.
  - split.
    + eapply nullableGamma_correct; eauto.
    + destruct (NtMap.find x fo) as [foSet |] eqn:Hfind.
      * destruct Hfm as [Hsou Hcom].
        eapply Hsou; eauto.
        apply in_elements_iff_in_set; auto.
      * inv Hin.
  - inv Hin.
Qed.

Lemma fromLookaheadList_preserves_in :
  forall x la gamma las,
    In (x, la, gamma) (fromLookaheadList x gamma las)
    -> In la las.
Proof.
  intros x la gamma las Hin.
  induction las; simpl in *.
  - inv Hin.
  - inv Hin.
    + inv H; auto.
    + right; auto.
Qed.

Lemma fromLookaheadList_preserves_lookahead_for :
  forall g x la gamma las,
    In (x, la, gamma) (fromLookaheadList x gamma las)
    -> (forall la', In la' las -> lookahead_for la' x gamma g)
    -> lookahead_for la x gamma g.
Proof.
  intros g x la gamma las Hin Hcor.
  apply Hcor.
  eapply fromLookaheadList_preserves_in; eauto.
Qed.
           
Lemma mkFirstEntries_sound :
  forall g nu fi x la gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> In (x, la, gamma) (mkFirstEntries x gamma nu fi)
    -> lookahead_for la x gamma g.
Proof.
  intros g nu fi x la gamma Hns Hfm Hin.
  eapply fromLookaheadList_preserves_lookahead_for; eauto.
  intros la' Hin'.
  left.
  eapply firstGamma_sound; eauto.
Qed.

Lemma mkFollowEntries_sound :
  forall g nu fo x la gamma,
    nullable_set_for nu g
    -> follow_map_for fo g
    -> In (x, la, gamma) (mkFollowEntries x gamma nu fo)
    -> lookahead_for la x gamma g.
Proof.
  intros g nu fo x la gamma Hns Hfm Hin.
  eapply fromLookaheadList_preserves_lookahead_for; eauto.
  intros la' Hin'.
  right.
  eapply followLookahead_sound; eauto.
Qed.
  
Lemma mkEntriesForProd_sound :
  forall g nu fi fo p x la gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> In (x, la, gamma) (mkEntriesForProd nu fi fo p)
    -> lookahead_for la x gamma g.
Proof.
  intros g nu fi fo p x la gamma Hns Hfi Hfo Hin.
  pose proof Hin as Hin'.
  apply mkEntriesForProd_preserves_prod in Hin'; subst.
  unfold mkEntriesForProd in Hin.
  apply in_app_or in Hin.
  inv Hin.
  - eapply mkFirstEntries_sound; eauto.
  - eapply mkFollowEntries_sound; eauto.
Qed.

Lemma mkEntriesForProd_complete :
  forall g nu fi fo x la gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> lookahead_for la x gamma g
    -> In (x, la, gamma) (mkEntriesForProd nu fi fo (x, gamma)).
Proof.
  intros g nu fi fo x la gamma Hnu Hfi Hfo Hlf.
  unfold mkEntriesForProd.
  apply in_or_app.
  inv Hlf.
  - left; admit.
  - right; admit.
Admitted.

Lemma mkParseTableEntries'_sound :
  forall g nu fi fo ps es,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> mkParseTableEntries' nu fi fo ps = es
    -> entries_correct_wrt_productions es ps g.
Proof.
  intros g nu fi fo ps.
  induction ps as [| p ps]; intros es Hnu Hfi Hfo Hmk; simpl in *; subst.
  - apply empty_entries_correct_wrt_empty_productions.
  - simpl in *.
    unfold entries_correct_wrt_productions.
    intros x la gamma.
    split; [intros Hin | intros [Hin Hlf]].
    + subst.
      apply in_app_or in Hin.
      destruct Hin.
      * split.
        -- left.
           destruct p as (x', gamma').
           apply mkEntriesForProd_preserves_prod in H; auto.
        -- eapply mkEntriesForProd_sound; eauto.
      * specialize IHps with
          (es := mkParseTableEntries' nu fi fo ps).
        unfold entries_correct_wrt_productions in IHps.
        apply IHps in H; auto.
        destruct H as [Hin Hlf].
        split; auto.
        right; auto.
    + subst.
      apply in_or_app.
      inv Hin.
      * left.
        eapply mkEntriesForProd_complete; eauto.
      * right.
        specialize (IHps (mkParseTableEntries' nu fi fo ps)).
        unfold entries_correct_wrt_productions in IHps.
        apply IHps; auto.
Admitted.
  
Lemma mkParseTableEntries_sound :
  forall g nu fi fo es,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> mkParseTableEntries nu fi fo g = es
    -> pt_entries_correct es g.
Proof.
  intros g nu fi fo es Hnu Hfi Hfo Hmk.
  apply invariant_iff_pt_entries_correct.
  unfold mkParseTableEntries in Hmk.
  eapply mkParseTableEntries'_sound; eauto.
Qed.

