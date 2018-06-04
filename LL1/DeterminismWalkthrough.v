Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable Lib.Utils
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof LL1.MonotonicityLemmas.
Import ListNotations.
Open Scope list_scope.

(* THIS SECTION CONTAINS COMPLETED LEMMAS *)

Lemma derivesForest_nil_nullable :
  forall f g gamma,
    (@derivesForest g) gamma [] f
    -> (@nullableGamma g) gamma.
Proof.
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall g x,
                (@derivesTree g) (NT x) nil tr
                -> (@nullableSym g) (NT x))
      (P0 := fun f =>
               forall g gamma,
                 (@derivesForest g) gamma nil f
                 -> (@nullableGamma g) gamma); intros.

  - inv H.
  - inv H.
    apply IHf in H5.
    econstructor.
    econstructor; eauto.
  - inv H.
    constructor.
  - destruct gamma.
    + constructor.
    + inv H.
      assert (prefix = nil) by
          (destruct prefix; try inv H2; auto).
      assert (suffix = nil) by
          (destruct prefix; try inv H2; auto).
      subst.
      inv H4.
      constructor.
      * apply IHf.
        econstructor; eauto.
      * apply IHf0.
        auto.
Qed.

Lemma derivesTree_nil_nullable :
  forall t g x,
    (@derivesTree g) (NT x) [] t
    -> (@nullableSym g) (NT x).
Proof.
  induction t using tree_mutual_ind with
      (P := fun tr =>
              forall g x,
                (@derivesTree g) (NT x) nil tr
                -> (@nullableSym g) (NT x))
      (P0 := fun f =>
               forall g gamma,
                 (@derivesForest g) gamma nil f
                 -> (@nullableGamma g) gamma); intros.

    - inv H.
  - inv H.
    apply IHt in H5.
    econstructor.
    econstructor; eauto.
  - inv H.
    constructor.
  - destruct gamma.
    + constructor.
    + inv H.
      assert (prefix = nil) by
          (destruct prefix; try inv H2; auto).
      assert (suffix = nil) by
          (destruct prefix; try inv H2; auto).
      subst.
      inv H4.
      constructor.
      * apply IHt.
        econstructor; eauto.
      * apply IHt0.
        auto.
Qed.

Lemma derivesForest_cons_firstGamma :
  forall f g tok toks gamma,
    (@derivesForest g) gamma (tok :: toks) f
    -> (@firstGamma g) (LA tok) gamma.
Proof.
  intro f.
  induction f using forest_mutual_ind with
      (P0 := fun f =>
              forall g tok toks gamma,
                (@derivesForest g) gamma (tok :: toks) f
                -> (@firstGamma g) (LA tok) gamma)
      (P := fun tr =>
               forall g tok toks x,
                 (@derivesTree g) x (tok :: toks) tr
                 -> (@firstSym g) (LA tok) x); intros.

  - inv H.
    constructor.

  - inv H.
    apply IHf with (tok := tok) (toks := toks) in H5.
    eapply FiNT.
    constructor; eauto.

  - inv H.

  - inv H.
    destruct prefix.
    + simpl in *.
      subst.
      apply IHf0 in H5.
      destruct hdRoot.
      * inv H4.
      * apply FiGammaTl.
        -- apply derivesTree_nil_nullable in H4.
           auto.
        -- auto.
    + simpl in *.
      inv H0.
      apply IHf in H4.
      apply FiGammaHd.
      auto.
Qed.

Lemma nullable_middle_sym :
  forall g xs ys sym,
    (@nullableGamma g) (xs ++ sym :: ys)
    -> (@nullableSym g) sym.
Proof.
  induction xs; intros.
  - simpl in H.
    inv H.
    auto.
  - eapply IHxs.
    inv H.
    eauto.
Qed.

Lemma gamma_with_terminal_not_nullable :
  forall g xs y zs,
    (@nullableGamma g) (xs ++ T y :: zs)
    -> False.
Proof.
  induction xs; intros.
  - simpl in H.
    inv H.
  - destruct a.
    + inv H.
    + inv H.
      eapply IHxs; eauto.
Qed.

Lemma nullable_split :
  forall g xs ys,
    (@nullableGamma g) (xs ++ ys)
    -> (@nullableGamma g) ys.
Proof.
  induction xs; intros.
  - auto.
  - inv H.
    eapply IHxs; eauto.
Qed.
  
Lemma no_first_follow_conflicts :
  forall tbl g,
    isParseTableFor tbl g
    -> forall la sym gamma,
      (@firstProd g) la sym gamma
      -> (@nullableProd g) sym gamma
      -> (@followProd g) la sym gamma
      -> False.
Proof.
  intros tbl g Htbl la sym gamma Hfi.
  destruct Htbl as [Hmin Hcom].
  induction Hfi using firstProd_mutual_ind with
      (P := fun la sym gamma
                (pf : (@firstProd g) la sym gamma) =>
              (@nullableProd g) sym gamma
              -> (@followProd g) la sym gamma
              -> False)
      (P0 := fun la gammaSuf
                 (pf : (@firstGamma g) la gammaSuf) =>
               forall sym gammaPre,
                 (@firstProd g) la sym (gammaPre ++ gammaSuf)
                 -> (@nullableProd g) sym (gammaPre ++ gammaSuf)
                 -> (@followProd g) la sym (gammaPre ++ gammaSuf)
                 -> False)
      (P1 := fun la sym (pf : (@firstSym g) la sym) =>
              (@nullableSym g) sym
              -> (@followSym g) la sym
              -> False).

  - intros Hnu Hfo.
    eapply IHHfi; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H in i.
      econstructor; eauto.
    + auto.
    + auto.

  - intros sym gammaSuf Hfi Hnu Hfo.
    eapply IHHfi.
    + inv Hnu.
      apply nullable_middle_sym in H0.
      auto.
    + destruct hd.
      * inv Hnu.
        apply gamma_with_terminal_not_nullable in H0.
        inv H0.
      * inv Hfo.
        inv Hnu.
        eapply FoLeft; eauto.
        assert (NT n :: tl = [NT n] ++ tl) by auto.
        rewrite H1 in H3.
        rewrite app_assoc in H3.
        eapply nullable_split in H3.
        auto.        

  - intros sym gammaPre Hfi Hnu Hfo.
    eapply IHHfi.
    + assert (NT x :: tl = [NT x] ++ tl) by auto.
      rewrite H in Hfi.
      rewrite app_assoc in Hfi.
      eauto.
    + rewrite <- app_assoc.
      simpl.
      auto.
    + rewrite <- app_assoc.
      simpl.
      auto.

  - intros Hnu Hfo.
    inv Hnu.
    inv H.

  - intros Hnu Hfo.
    inv Hnu.
    inv H.
    assert (Hlk : (@isLookaheadFor g) la (NT x) gamma).
    { unfold isLookaheadFor.
      left.
      auto. }
    assert (Hlk' : (@isLookaheadFor g) la (NT x) ys).
    { unfold isLookaheadFor.
      right.
      split.
      { constructor; auto. }
      { constructor; auto. }}
    unfold ptComplete in Hcom.
    apply Hcom in Hlk; apply Hcom in Hlk'.
    destruct Hlk as [laMap [Hsf Hlf]].
    destruct Hlk' as [laMap' [Hsf' Hlf']].
    assert (gamma = ys) by congruence.
    subst.
    apply IHHfi.
    + constructor; auto.
    + constructor; auto.
Qed.

Lemma firstGamma_split :
  forall g la xs ys,
    (@firstGamma g) la xs
    -> (@firstGamma g) la (xs ++ ys).
Proof.
  induction xs; intros.
  - inv H.
  - inv H.
    + constructor; auto.
    + eapply FiGammaTl; eauto.
Qed.

 Fixpoint appF f f2 :=
   match f with
   | Fnil => f2
   | Fcons tr f' => Fcons tr (appF f' f2)
   end.

Lemma appF_nil_r : forall f,
    appF f Fnil = f.
Proof.
  induction f; simpl.
  - auto.
  - rewrite IHf. auto.
Qed.

Lemma appF_nil_l : forall f,
    appF Fnil f = f.
Proof.
  intros. simpl. auto.
Qed.

Lemma derives_app :
  forall g gPre gSuf wPre wSuf fPre fSuf,
    (@derivesForest g) gPre wPre fPre
    -> (@derivesForest g) gSuf wSuf fSuf
    -> (@derivesForest g) (gPre ++ gSuf)
                          (wPre ++ wSuf)
                          (appF fPre fSuf).
Proof.
  induction gPre; intros; simpl in *.
  - inv H.
    auto.
  - inv H.
    simpl.
    rewrite <- app_assoc.
    constructor.
    + auto.
    + apply IHgPre; auto.
Qed.

Lemma prefixes_eq :
  forall (suf pre pre' : list string),
    app pre suf = app pre' suf
    -> pre = pre'.
Proof.
  induction suf; intros; simpl in *.
  - repeat rewrite app_nil_r in H.
    auto.
  - assert (a :: suf = app [a] suf) by auto.
    repeat rewrite H0 in H.
    repeat rewrite app_assoc in H.
    apply IHsuf in H.
    apply app_inj_tail in H.
    destruct H.
    auto.
Qed.

Lemma suffixes_eq :
  forall (pre suf suf' : list string),
    app pre suf = app pre suf'
    -> suf = suf'.
Proof.
  induction pre; intros; simpl in *.
  - auto.
  - inv H.
    apply IHpre; auto.
Qed.

(* This is a version of the determinism proof from the
   Rosenkrantz paper, which describes only the determinism
   of the derivation, not the structure of the generated
   parse tree *)
Lemma rosenkrantz_lemma_4 :
  forall tbl g,
    isParseTableFor tbl g
    -> forall lx gpre rx gamma gsuf
              wpre wmid wsuf
              fpre fmid fsuf,
      In (lx, gpre ++ NT rx :: gsuf) (productions g)
      -> In (rx, gamma) (productions g)
      -> (@derivesForest g) gpre wpre fpre
      -> (@derivesForest g) gamma wmid fmid
      -> (@derivesForest g) gsuf wsuf fsuf
      -> forall gamma' fmid',
          In (rx, gamma') (productions g)
          -> (@derivesForest g) gamma' wmid fmid'
          -> gamma = gamma'.
Proof.
  intros.
  destruct H as [Hmin Hcom].
  destruct wmid as [| tok toks].
  - apply derivesForest_nil_nullable in H3.
    apply derivesForest_nil_nullable in H6.
    assert (Hlk : (@isLookaheadFor g) EOF (NT rx) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT rx) gamma').
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma') by congruence.
      auto.
  - apply derivesForest_cons_firstGamma in H3.
    apply derivesForest_cons_firstGamma in H6.
    assert (Hlk : (@isLookaheadFor g) (LA tok) (NT rx) gamma).
    { unfold isLookaheadFor.
      left.
      constructor; auto. }
    assert (Hlk' : (@isLookaheadFor g) (LA tok) (NT rx) gamma').
    { unfold isLookaheadFor.
      left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma') by congruence.
      auto.
Qed.

(* This is a modified version of the previous lemma that 
   doesn't require wmid to be the same in the statements 
   about gamma and gamma'. It says that whenever wmid and
   wmid' are two possibly different prefixes of the same 
   word, gamma and gamma' must be equal.

   Maybe I can also prove that wmid = wmid' and 
   wsuf = wsuf' ? *)
Lemma rosenkrantz_lemma_4' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall lx gpre rx gamma gsuf
              wpre wmid wsuf
              fpre fmid fsuf,
      In (lx, gpre ++ NT rx :: gsuf) (productions g)
      -> In (rx, gamma) (productions g)
      -> (@derivesForest g) gpre wpre fpre
      -> (@derivesForest g) gamma wmid fmid
      -> (@derivesForest g) gsuf wsuf fsuf
      -> forall wmid' wsuf' gamma' fmid' fsuf',
          In (rx, gamma') (productions g)
          -> (@derivesForest g) gamma' wmid' fmid'
          -> (@derivesForest g) gsuf wsuf' fsuf'
          -> wmid ++ wsuf = wmid' ++ wsuf'
          -> gamma = gamma'.
Proof.
  intros.
  pose proof H as H'.
  destruct H as [Hmin Hcom].
  destruct wmid as [| mtok mtoks].
  - destruct wmid' as [| mtok' mtoks'].
    + apply derivesForest_nil_nullable in H3.
      apply derivesForest_nil_nullable in H6.
      assert (Hlk : (@isLookaheadFor g) EOF (NT rx) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT rx) gamma').
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma') by congruence.
      auto.
    + destruct wsuf as [| stok stoks].
      * inv H8.
      * (* first/follow conflict *)
        exfalso.
        inv H8.
        assert (Hlk : (@isLookaheadFor g)
                        (LA mtok')
                        (NT rx)
                        gamma).
          { unfold isLookaheadFor.
            right.
            split.
            { constructor; auto.
              apply derivesForest_nil_nullable in H3.
              auto. }
            { constructor; auto.
              eapply FoRight; eauto.
              apply derivesForest_cons_firstGamma in H4.
              auto. }}
          assert (Hlk' : (@isLookaheadFor g)
                           (LA mtok')
                           (NT rx)
                           gamma').
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesForest_cons_firstGamma in H6.
            auto. }
          unfold ptComplete in Hcom.
          apply Hcom in Hlk; apply Hcom in Hlk'.
          destruct Hlk as [laMap [Hsf Hlf]].
          destruct Hlk' as [laMap' [Hsf' Hlf']].
          assert (gamma = gamma') by congruence.
          subst.
          assert ((@firstProd g)
                    (LA mtok')
                    (NT rx) gamma').
          { constructor; auto.
            apply derivesForest_cons_firstGamma in H6.
            auto. }
          assert ((@nullableProd g) (NT rx) gamma').
          { constructor; auto.
            apply derivesForest_nil_nullable in H3.
            auto. }
          assert ((@followProd g)
                    (LA mtok')
                    (NT rx) gamma').
          { constructor; auto.
            econstructor; eauto.
            apply derivesForest_cons_firstGamma in H4.
            auto. }
          eapply no_first_follow_conflicts; eauto.
  - destruct wmid' as [| mtok' mtoks']; simpl in *; subst.
    + (* another first/follow conflict *)
      exfalso.
      assert (Hlk : (@isLookaheadFor g)
                      (LA mtok)
                      (NT rx)
                      gamma').
      { unfold isLookaheadFor.
        right.
        split.
        { constructor; auto.
          apply derivesForest_nil_nullable in H6.
          auto. }
        { constructor; auto.
          eapply FoRight; eauto.
          apply derivesForest_cons_firstGamma in H7.
          auto. }}
      assert (Hlk' : (@isLookaheadFor g)
                       (LA mtok)
                       (NT rx)
                       gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto.
        apply derivesForest_cons_firstGamma in H3.
        auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk; apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma') by congruence.
      subst.
      assert ((@firstProd g)
                (LA mtok)
                (NT rx) gamma').
      { constructor; auto.
        apply derivesForest_cons_firstGamma in H3.
        auto. }
      assert ((@nullableProd g) (NT rx) gamma').
      { constructor; auto.
        apply derivesForest_nil_nullable in H6.
        auto. }
      assert ((@followProd g)
                (LA mtok)
                (NT rx) gamma').
      { constructor; auto.
        econstructor; eauto.
        apply derivesForest_cons_firstGamma in H7.
        auto. }
      eapply no_first_follow_conflicts; eauto.
    + inv H8.
      apply derivesForest_cons_firstGamma in H3.
      apply derivesForest_cons_firstGamma in H6.
      assert (Hlk : (@isLookaheadFor g)
                      (LA mtok')
                      (NT rx)
                      gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g)
                       (LA mtok')
                       (NT rx)
                       gamma').
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma') by congruence.
      auto.
Qed.

(* THE NEXT SECTION CONTAINS DIFFERENT ATTEMPTS AT PROVING
   DETERMINISM OF LL(1) DERIVATIONS *)

(* Here's a natural-seeming way of stating the
   determinism property, although it turns out to be
   incomplete *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesTree g) sym word tr
      -> (@derivesTree g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesForest g) gamma word f
                 -> (@derivesForest g) gamma word f'
                 -> f = f'); intros.
  - inv H; inv H0; auto.

  - inv H; inv H0.
    (* We can derive the fact that gamma = gamma0 from the
       fact that the grammar is LL(1). I'll demonstrate how
       to do this in the next example. *)
    assert (gamma0 = gamma) by admit. 
    subst.
    erewrite IHtr; eauto.

  - inv H; inv H0; auto.

  - inv H.
    inv H0.
    (* Here, we're going to get stuck because we don't know
       whether prefix = prefix0, so we can't use either IH.
       In general, though, our P0 property isn't necessarily
       true of any gamma -- only a gamma that appears as part
       of a right-hand side of some grammar production. *)
Abort.

(* In this attempt, I show how to prove that when two 
   productions with the same left-hand nonterminal
   derive a word, their right-hand sides must be the same.

   I also modify the P0 to specify that gamma must be part
   of the right-hand side of some production. *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesTree g) sym word tr
      -> (@derivesTree g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall fsuf' x gpre gsuf wsuf,
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gsuf wsuf fsuf
                 -> derivesForest gsuf wsuf fsuf'
                 -> fsuf = fsuf'); intros.
  
  - inv H; inv H0; auto.

  - inv H; inv H0.
    (* Here, we can prove that gamma = gamma0 using an approach
       similar to the one in the Rosenkrantz lemma above. *)
    assert (gamma0 = gamma).
    { destruct word as [| tok toks].
      apply derivesForest_nil_nullable in H2.
      apply derivesForest_nil_nullable in H6.
      assert (Hlk : (@isLookaheadFor g) EOF (NT s) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT s) gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      auto.
  - apply derivesForest_cons_firstGamma in H2.
    apply derivesForest_cons_firstGamma in H6.
    assert (Hlk : (@isLookaheadFor g) (LA tok) (NT s) gamma).
    { unfold isLookaheadFor.
      left.
      constructor; auto. }
    assert (Hlk' : (@isLookaheadFor g) (LA tok) (NT s) gamma0).
    { unfold isLookaheadFor.
      left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      auto. }
    subst.
    erewrite IHtr with (gpre := nil); eauto.

  - inv H0; inv H1; auto.

  - inv H0.
    inv H1.
    (* Here, we're still stuck because we don't know whether
       the prefixes are equal (or whether the suffixes are
       equal). This makes the IH's useless, because they only
       apply when we already know that the strings are equal,
       so they need to be generalized. *)
Abort.

(* In this attempt, I try to prove that each symbol on the
   right-hand side of a production and the symbols to its
   right can only split the input in one way. *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gpre sym gsuf
              wpre wpre' wsuf wsuf'
              fsuf fsuf',
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesTree g) sym wpre tr
      -> (@derivesTree g) sym wpre' tr'
      -> (@derivesForest g) gsuf wsuf fsuf
      -> (@derivesForest g) gsuf wsuf' fsuf'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> wpre = wpre'
         /\ wsuf = wsuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall fsuf' x gpre gsuf
                      wpre wpre' wsuf wsuf'
                      fpre fpre',
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gpre wpre fpre
                 -> derivesForest gpre wpre' fpre'
                 -> derivesForest gsuf wsuf fsuf
                 -> derivesForest gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf'); intros.
  
  - inv H0; inv H1.
    inv H4.
    repeat (split; auto).

  - inv H0; inv H1.
    assert (gamma0 = gamma) by admit; subst.
    (* This is looking good, but if we try to apply IHtr
       to one of our other hypotheses, we run into trouble
       because it expects gpre and gsuf to appear in the
       same production, whereas the gamma in our hypotheses
       appears a level below gsuf. *)
    eapply IHtr with
        (gpre := nil)
        (wpre := nil)
        (wpre' := nil) in H6; eauto.
    + destruct H6.
      destruct H1.
      subst.
      apply suffixes_eq in H4.
      repeat (split; auto).
    + constructor.
    + constructor.
    + (* We can't prove this append fact, so we're stuck *)
Abort.

(* In this attempt, I try to prove that each symbol on the
   right-hand side of a production and the symbols to its
   right can only split the input in one way. *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gpre sym gsuf
              wpre wpre' wsuf wsuf'
              fsuf fsuf',
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesTree g) sym wpre tr
      -> (@derivesTree g) sym wpre' tr'
      -> (@derivesForest g) gsuf wsuf fsuf
      -> (@derivesForest g) gsuf wsuf' fsuf'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> wpre = wpre'
         /\ wsuf = wsuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall fsuf' x gpre gsuf
                      wpre wpre' wsuf wsuf'
                      fpre fpre',
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gpre wpre fpre
                 -> derivesForest gpre wpre' fpre'
                 -> derivesForest gsuf wsuf fsuf
                 -> derivesForest gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf'); intros.
  
  - inv H0; inv H1.
    inv H4.
    repeat (split; auto).

  - inv H0; inv H1.
    assert (gamma0 = gamma) by admit; subst.
    (* This is looking good, but if we try to apply IHtr
       to one of our other hypotheses, we run into trouble
       because it expects gpre and gsuf to appear in the
       same production, whereas the gamma in our hypotheses
       appears a level below gsuf. *)
    eapply IHtr with
        (gpre := nil)
        (wpre := nil)
        (wpre' := nil) in H6; eauto.
    + destruct H6.
      destruct H1.
      subst.
      apply suffixes_eq in H4.
      repeat (split; auto).
    + constructor.
    + constructor.
    + (* We can't prove this append fact, so we're stuck *)
Abort.

