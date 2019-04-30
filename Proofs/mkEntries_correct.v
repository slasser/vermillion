Require Import List.

Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Require Import mkFollowMap_correct.
Import ListNotations.

Module EntryProofsFn (Import G : Grammar.T).

  Module Import L := LemmasFn G.
  Module Export FollowProofs := FollowProofsFn G.

  Definition entries_correct es g :=
    forall xp la,
      In (xp, la) es
      <-> In xp g.(prods)
          /\ lookahead_for la (lhs xp) (rhs xp) g.

  (* invariant relating a list of entries to a list of productions *)
  Definition entries_correct_wrt_productions es xps g :=
    forall xp la,
      In (xp, la) es <-> In xp xps /\ lookahead_for la (lhs xp) (rhs xp) g.

  Lemma invariant_iff_entries_correct :
    forall g es,
      entries_correct_wrt_productions es g.(prods) g 
      <-> entries_correct es g.
  Proof.
    split; intros; auto.
  Qed.

  Lemma empty_entries_correct_wrt_empty_productions :
    forall g,
      entries_correct_wrt_productions [] [] g.
  Proof.
    intros g.
    split; [intros Hin | intros [Hin _]]; inv Hin.
  Qed.

  Lemma fromLookaheadList_preserves_prod :
    forall xp xp' la las,
      In (xp, la) (fromLookaheadList xp' las)
      -> xp = xp'.
  Proof.
    intros xp xp' la las Hin.
    induction las as [| la' las]; simpl in *.
    - inv Hin.
    - inv Hin.
      + inv H; auto.
      + apply IHlas; auto.
  Qed.

  Lemma entriesForProd_preserves_prod :
    forall xp xp' la nu fi fo,
      In (xp, la) (entriesForProd nu fi fo xp')
      -> xp = xp'.
  Proof.
    intros xp xp' la nu fi fo Hin.
    unfold entriesForProd in Hin.
    apply in_app_or in Hin.
    destruct Hin; eapply fromLookaheadList_preserves_prod; eauto.
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
      -> In la (firstGamma' gamma nu fi)
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
                ** apply in_elements_iff_in_laSet; auto.
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
             apply in_elements_iff_in_laSet; auto.
          -- inv Hin.
  Qed.

  (* There's probably a way to shorten this *)
  Lemma firstGamma_complete :
    forall g la nu fi gamma,
      nullable_set_for nu g
      -> first_map_for fi g
      -> first_gamma g la gamma
      -> In la (firstGamma' gamma nu fi).
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
                apply in_elements_iff_in_laSet; auto.
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
                apply in_elements_iff_in_laSet; auto.
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
          apply in_elements_iff_in_laSet; auto.
        * inv Hin.
    - inv Hin.
  Qed.

  Lemma fromLookaheadList_preserves_in :
    forall xp la las,
      In (xp, la) (fromLookaheadList xp las) <-> In la las.
  Proof.
    intros xp la las.
    split; intros Hin.
    - induction las; simpl in *; auto.
      inv Hin; auto.
      inv H; auto.
    - induction las; simpl in *; auto.
      inv Hin; auto.
  Qed.

  Lemma fromLookaheadList_preserves_soundness :
    forall g xp la las,
      In (xp, la) (fromLookaheadList xp las)
      -> (forall la', In la' las -> lookahead_for la' (lhs xp) (rhs xp) g)
      -> lookahead_for la (lhs xp) (rhs xp) g.
  Proof.
    intros g xp la las Hin Hcor.
    apply Hcor.
    eapply fromLookaheadList_preserves_in; eauto.
  Qed.

  Lemma firstEntries_sound :
    forall g nu fi xp la,
      nullable_set_for nu g
      -> first_map_for fi g
      -> In (xp, la) (firstEntries xp nu fi)
      -> lookahead_for la (lhs xp) (rhs xp) g.
  Proof.
    intros g nu fi xp la Hns Hfm Hin.
    eapply fromLookaheadList_preserves_soundness; eauto.
    intros la' Hin'.
    left; eapply firstGamma_sound; eauto.
  Qed.

  Lemma followEntries_sound :
    forall g nu fo xp la,
      nullable_set_for nu g
      -> follow_map_for fo g
      -> In (xp, la) (followEntries xp nu fo)
      -> lookahead_for la (lhs xp) (rhs xp) g.
  Proof.
    intros g nu fo xp la Hns Hfm Hin.
    eapply fromLookaheadList_preserves_soundness; eauto.
    intros la' Hin'.
    right; eapply followLookahead_sound; eauto.
  Qed.
  
  Lemma entriesForProd_sound :
    forall g nu fi fo xp xp' la,
      nullable_set_for nu g
      -> first_map_for fi g
      -> follow_map_for fo g
      -> In (xp, la) (entriesForProd nu fi fo xp')
      -> lookahead_for la (lhs xp) (rhs xp) g.
  Proof.
    intros g nu fi fo xp xp' la Hns Hfi Hfo Hin.
    pose proof Hin as Hin'.
    apply entriesForProd_preserves_prod in Hin'; subst.
    unfold entriesForProd in Hin.
    apply in_app_or in Hin; destruct Hin.
    - eapply firstEntries_sound; eauto.
    - eapply followEntries_sound; eauto.
  Qed.

  Lemma fromLookaheadList_preserves_list_completeness :
    forall P xp la las,
      P la
      -> (forall la', P la' -> In la' las)
      -> In (xp, la) (fromLookaheadList xp las).
  Proof.
    intros P xp la las Hp Hcor.
    apply fromLookaheadList_preserves_in; auto.
  Qed.

  Lemma firstEntries_complete :
    forall g nu fi xp la,
      nullable_set_for nu g
      -> first_map_for fi g
      -> first_gamma g la (rhs xp)
      -> In (xp, la) (firstEntries xp nu fi).
  Proof.
    intros g nu fi xp la Hnu Hfi Hfg.
    unfold firstEntries.
    eapply fromLookaheadList_preserves_list_completeness with
        (P := fun la => first_gamma g la (rhs xp)); auto.
    intros la' Hfg'.
    eapply firstGamma_complete; eauto.
  Qed.

  Lemma followLookahead_complete :
    forall g nu fo xp la,
      nullable_set_for nu g
      -> follow_map_for fo g
      -> nullable_gamma g (rhs xp)
      -> follow_sym g la (NT (lhs xp))
      -> In la (followLookahead (lhs xp) (rhs xp) nu fo).
  Proof.
    intros g nu fo xp la Hns Hfm Hng Hfs.
    unfold followLookahead.
    eapply nullableGamma_correct in Hng; eauto.
    rewrite Hng.
    destruct Hfm as [Hsou Hcom].
    eapply Hcom in Hfs.
    destruct Hfs as [xFollow [Hnf Hli]]; auto.
    rewrite Hnf.
    apply in_elements_iff_in_laSet; auto.
  Qed.

  Lemma followEntries_complete :
    forall g nu fo xp la,
      nullable_set_for nu g
      -> follow_map_for fo g
      -> nullable_gamma g (rhs xp)
      -> follow_sym g la (NT (lhs xp))
      -> In (xp, la) (followEntries xp nu fo).
  Proof.
    intros g nu fo xp la Hns Hfm Hng Hfs.
    unfold followEntries.
    apply fromLookaheadList_preserves_list_completeness with
        (P := fun la => follow_sym g la (NT (lhs xp))); auto.
    intros la' Hfs'.
    eapply followLookahead_complete; eauto.
  Qed.

  Lemma entriesForProd_complete :
    forall g nu fi fo xp la,
      nullable_set_for nu g
      -> first_map_for fi g
      -> follow_map_for fo g
      -> lookahead_for la (lhs xp) (rhs xp) g
      -> In (xp, la) (entriesForProd nu fi fo xp).
  Proof.
    intros g nu fi fo xp la Hnu Hfi Hfo Hlf.
    unfold entriesForProd.
    apply in_or_app; inv Hlf.
    - left; eapply firstEntries_complete; eauto.
    - destruct H.
      right; eapply followEntries_complete; eauto.
  Qed.

  Lemma mkEntries'_correct :
    forall g nu fi fo,
      nullable_set_for nu g
      -> first_map_for fi g
      -> follow_map_for fo g
      -> forall xps es,
          mkEntries' nu fi fo xps = es
          -> entries_correct_wrt_productions es xps g.
  Proof.
    intros g nu fi fo Hnu Hfi Hfo xps.
    induction xps as [| xp xps]; intros es Hmk; simpl in *; subst.
    - apply empty_entries_correct_wrt_empty_productions.
    - unfold entries_correct_wrt_productions.
      intros xp' la.
      split; [intros Hin | intros [Hin Hlf]].
      + apply in_app_or in Hin.
        destruct Hin.
        * split.
          -- left; apply entriesForProd_preserves_prod in H; auto.
          -- eapply entriesForProd_sound; eauto.
        * specialize IHxps with
              (es := mkEntries' nu fi fo xps).
          unfold entries_correct_wrt_productions in IHxps.
          apply IHxps in H; auto.
          destruct H as [Hin Hlf].
          split; auto.
          right; auto.
      + subst.
        apply in_or_app.
        inv Hin.
        * left.
          eapply entriesForProd_complete; eauto.
        * right.
          specialize (IHxps (mkEntries' nu fi fo xps)).
          unfold entries_correct_wrt_productions in IHxps.
          apply IHxps; auto.
  Qed.
  
  Theorem mkEntries_correct :
    forall (g  : grammar)
           (nu : NtSet.t)
           (fi : first_map)
           (fo : follow_map) 
           (es : list table_entry),
      nullable_set_for nu g
      -> first_map_for fi g
      -> follow_map_for fo g
      -> mkEntries nu fi fo g = es
      -> entries_correct es g.
  Proof.
    intros g nu fi fo es Hnu Hfi Hfo Hmk.
    apply invariant_iff_entries_correct.
    unfold mkEntries in Hmk.
    eapply mkEntries'_correct; eauto.
  Qed.

End EntryProofsFn.

