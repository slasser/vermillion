Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

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

Lemma first_gamma_nu_tail :
  forall g la x syms,
    nullable_sym g (NT x)
    -> first_gamma g la syms
    -> first_gamma g la (NT x :: syms).
Proof.
Admitted.

Lemma firstGamma_correct :
  forall g la nu fi gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> In la (firstGamma gamma nu fi)
       <-> first_gamma g la gamma.
Proof.
  intros g la nu fi gamma Hns Hfm.
  split.
  - intros Hin.
    induction gamma as [| sym syms]; simpl in *.
    + inv Hin.
    + destruct sym as [y | x].
      * inv Hin.
        -- apply FirstGamma with (gpre := nil); auto.
        -- inv H.
      * destruct (NtSet.mem x nu) eqn:Hmem.
        -- destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
           ++ apply in_app_or in Hin.
              inv Hin.
              ** (* la is in FIRST(X) *)
                 destruct Hfm as [Hsou Hcom].
                 unfold first_map_sound in Hsou.
                 apply Hsou with (la := la) in Hfind.
                 --- apply FirstGamma with (gpre := nil); auto.
                 --- admit.
              ** apply first_gamma_nu_tail; auto.
                 destruct Hns as [Hsou Hcom].
                 apply Hsou.
                 apply NtSet.mem_spec; auto.
           ++ simpl in *.
              apply first_gamma_nu_tail; auto.
              destruct Hns as [Hsou Hcom].
              apply Hsou.
              apply NtSet.mem_spec; auto.
        -- destruct (NtMap.find x fi) as [fiSet |] eqn:Hfind.
           ++ destruct Hfm as [Hsou com].
              eapply Hsou in Hfind.
              apply FirstGamma with (gpre := nil); auto.
              apply Hfind.
              admit.
           ++ inv Hin.
  - admit.
Admitted.
         
Lemma mkFirstEntries_sound :
  forall g nu fi x la gamma,
    In (x, la, gamma) (mkFirstEntries x gamma nu fi)
    -> first_gamma g la gamma.
Proof.
  intros g nu fi x la gamma Hin.
  unfold mkFirstEntries in Hin.
Admitted.

Lemma mkEntriesForProd_sound :
  forall g nu fi fo p x la gamma,
    In (x, la, gamma) (mkEntriesForProd nu fi fo p)
    -> lookahead_for la x gamma g.
Proof.
  intros g nu fi fo p x la gamma Hin.
  pose proof Hin as Hin'.
  apply mkEntriesForProd_preserves_prod in Hin'; subst.
  unfold mkEntriesForProd in Hin.
  apply in_app_or in Hin.
  inv Hin.
  - left.
    eapply mkFirstEntries_sound; eauto.
  - admit.
Admitted.

Lemma mkParseTableEntries'_sound :
  forall g nu fi fo ps es,
    mkParseTableEntries' nu fi fo ps = es
    -> entries_correct_wrt_productions es ps g.
Proof.
  intros g nu fi fo ps.
  induction ps as [| p ps]; intros es Hmk; simpl in *; subst.
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
        -- admit.
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
      * admit. (* need lemma about mkEntriesForProd *)
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

