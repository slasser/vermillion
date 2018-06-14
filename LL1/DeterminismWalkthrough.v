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

Fixpoint inF tr f :=
  match f with
  | Fnil => False
  | Fcons tr' f' => tr = tr' \/ inF tr f'
  end.



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
  induction tr using tree_nested_ind with
      (Q := fun f =>
              forall x gpre gsuf word,
                In (x, gpre ++ gsuf) (productions g)
                -> derivesForest gsuf word f
                -> forall tr tr' sym w,
                    inF tr f
                    -> derivesTree sym w tr
                    -> derivesTree sym w tr'
                    -> tr = tr); intros.

  - inv H0.
    inv H1.
    assert (
    
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               (forall f' x gpre sym gsuf
                      wpre wpre' wsuf wsuf'
                      tr tr',
                 In (x, gpre ++ sym :: gsuf) (productions g)
                 -> derivesTree sym wpre tr
                 -> derivesTree sym wpre' tr'
                 -> derivesForest gsuf wsuf f
                 -> derivesForest gsuf wsuf' f'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf')
               /\ (forall f' lx gpre rx gsuf gsuf2,
                      In (lx, gpre ++ NT rx :: gsuf)
                         (productions g)
                      -> derivesForest gsuf2 wpre f
                      -> derivesForest gsuf2 wpre' f'
                      -> derivesForest gsuf wsuf fsuf
                      -> derivesForest gsuf wsuf' fsuf'
                      -> wpre ++ wsuf = wpre' ++ wsuf'
                      -> wpre = wpre' /\ wsuf = wsuf' /\
                         fsuf = fsuf')

               ; intros.
  - inv H0; inv H1; inv H4; auto.
  - inv H0; inv H1.
    assert (gamma0 = gamma) by admit; subst.
    





Inductive ForallF (P : tree -> Prop) : forest -> Prop :=
| ForallFnil : ForallF P Fnil
| ForallFcons : forall tr f',
    P tr -> ForallF P f' -> ForallF P (Fcons tr f').

Inductive tree_det {g : grammar} :
  symbol -> list string -> tree -> Prop :=
| Leaf_det :
    forall y word,
    (forall word' tr',
        (@derivesTree g) (T y) word (Leaf y)
        -> (@derivesTree g) (T y) word' tr'
        -> word = word')
    -> tree_det (T y) word (Leaf y)
| Node_det :
    forall x gamma word f,
      In (x, gamma) (productions g)
      -> forest_det gamma word f
      -> tree_det (NT x) word (Node x f)
with forest_det {g : grammar} :
        list symbol -> list string -> forest -> Prop :=
     | Fnil_det :
         forest_det nil nil Fnil
     | Fcons_det :
         forall hd tl wpre wsuf tr f,
           tree_det hd wpre tr
           -> forest_det tl wsuf f
           -> (forall wpre' wsuf' tr' f',
                  wpre ++ wsuf = wpre' ++ wsuf'
                  -> (@derivesTree g) hd wpre tr
                  -> (@derivesTree g) hd wpre' tr'
                  -> (@derivesForest g) tl wsuf f
                  -> (@derivesForest g) tl wsuf' f'
                  -> wpre = wpre'
                     /\ wsuf = wsuf')
           -> forest_det (hd :: tl) (wpre ++ wsuf) (Fcons tr f).

Lemma ll1_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym word,
      (@derivesTree g) sym word tr
      -> (@tree_det g) sym word tr.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall sym word,
                (@derivesTree g) sym word tr
                -> (@tree_det g) sym word tr)
      (P0 := fun f =>
               forall x gpre gsuf word,
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gsuf word f
                 -> (@forest_det g) gsuf word f); intros.

  - inv H.
    constructor; intros.
    inv H0.
    auto.
  - inv H.
    econstructor; intros; eauto.
    eapply IHtr with (gpre := nil); eauto.
  - inv H0.
    constructor.
  - inv H0.
    constructor; intros.
    + eapply IHtr; auto.
    + eapply IHtr0 with (gpre := gpre ++ [hdRoot]); eauto.
      admit.
    + eapply IHtr in H5.
      
    constructor.
               forall 
              forall x gpre sym gsuf wpre wsuf fsuf,
                In (x, gpre ++ sym :: gsuf) (productions g)
                -> (@derivesTree g) sym wpre tr
                -> (@derivesForest g) gsuf wsuf fsuf
                -> (@tree_det g) tr)
      (P0 := fun f =>
               forall x gpre gsuf word,
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gsuf word f
                 -> (@forest_det g) f); intros.

  - inv H0.
    econstructor; intros; constructor; auto.
  - inv H0.
    constructor; intros.
    + eapply IHtr with (gpre := nil); eauto.
    + assert (gamma0 = gamma') by admit; 


    constructor.
  - inv H.
    constructor; intros.
    + eapply IHtr with (gpre := nil); eauto.
    + admit.
  - constructor.
  - inv H0.
    constructor; intros.
    + eapply IHtr; eauto.
    + eapply IHtr0 with (gpre := gpre ++ [hdRoot]); eauto.
      assert (hdRoot :: tlRoots = [hdRoot] ++ tlRoots) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      eauto.
    + induction gpre.
      * eapply IHtr0 with (gpre := gpre ++ [hdRoot]) in H6;
        eauto.
      * inv H6.
        -- inv H3; inv H4.
           repeat rewrite app_nil_r in *.
           auto.
        -- inv H3; inv H4.

          
      assert (hdRoot :: tlRoots = [hdRoot] ++ tlRoots) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      eauto.eapply IHtr0 in 
















      

Inductive tree_det' {g : grammar} :
  tree -> Prop :=
| Leaf_det' :
    forall y,
      tree_det' (Leaf y)
| Node_det' :
    forall x f,
      forest_det' f
      -> (forall lx f' gamma gamma' wpre wpre' wsuf wsuf'
             fsuf fsuf' gpre gsuf,
             In (lx, gpre ++ NT x :: gsuf) (productions g)
             -> In (x, gamma) (productions g)
             -> In (x, gamma') (productions g)
             -> (@derivesForest g) gamma wpre f
             -> (@derivesForest g) gamma' wpre' f'
             -> (@derivesForest g) gsuf wsuf fsuf
             -> (@derivesForest g) gsuf wsuf' fsuf'
             -> wpre ++ wsuf = wpre' ++ wsuf'
             -> gamma = gamma' /\ wpre = wpre' /\ wsuf = wsuf')
      -> tree_det' (Node x f)
with forest_det' {g : grammar} :
       forest -> Prop :=
     | Fnil_det' : forest_det' Fnil
     | Fcons_det' :
         forall tr f,
           tree_det' tr
           -> forest_det' f
           -> (forall hd tl wpre wpre' wsuf wsuf' tr' f',
                  wpre ++ wsuf = wpre' ++ wsuf'
                  -> (@derivesTree g) hd wpre tr
                  -> (@derivesTree g) hd wpre' tr'
                  -> (@derivesForest g) tl wsuf f
                  -> (@derivesForest g) tl wsuf' f'
                  -> wpre = wpre'
                     /\ wsuf = wsuf')
           -> forest_det' (Fcons tr f).

Lemma ll1_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym word,
      (@derivesTree g) sym word tr
      -> (@tree_det' g) tr.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall sym word,
              derivesTree sym word tr -> tree_det' tr)
      (P0 := fun f =>
               forall x gpre gsuf word,
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gsuf word f ->
                 forest_det' f); intros.
  - constructor.
  - inv H.
    constructor; intros.
    + eapply IHtr with (gpre := nil) ; eauto.
    + assert (gamma0 = gamma') by admit.
      subst.
      






  

Definition tree_det' {g : grammar} tr :=
  forall sym word tr',
    (@derivesTree g) sym word tr
    -> (@derivesTree g) sym word tr'
    -> tr = tr'.

Definition forest_det' {g : grammar} f :=
  forall gamma word f',
    (@derivesForest g) gamma word f
    -> (@derivesForest g) gamma word f'
    -> f = f'.

Lemma det_det' :
  forall g tr,
    (@tree_det g) tr -> (@tree_det' g) tr.
Proof.
  intros g.
  induction tr using tree_mutual_ind with
      (P := fun tr => (@tree_det g) tr -> (@tree_det' g) tr)
      (P0 := fun f => (@forest_det g) f -> (@forest_det' g) f)
  ; intros.
  - unfold tree_det'; intros.
    inv H0; inv H1; auto.
  - inv H.
    unfold tree_det'; intros.
    inv H; inv H0.
    pose proof H4 as H4'.
    eapply H3 with (gamma := gamma) in H4; eauto; subst.
    apply IHtr in H2.
    unfold forest_det' in H2.
    erewrite H2; eauto.
  - unfold forest_det'; intros.
    inv H0; inv H1; auto.
  - inv H.
    unfold forest_det'; intros.
    inv H; inv H0.
    pose proof H10 as H10'.
    eapply H4 with (wpre := prefix)
                   (wsuf := suffix) in H10; eauto.
    destruct H10; subst.
    eapply IHtr in H2.
    unfold tree_det' in H2.
    erewrite H2; eauto.
    eapply IHtr0 in H3.
    unfold forest_det' in H3.
    erewrite H3; eauto.
Qed.
    
Section list_length_ind.  
  Variable A : Type.
  Variable P : list A -> Prop.

  Hypothesis H : forall xs, (forall l, List.length l < List.length xs -> P l) -> P xs.

  Theorem list_length_ind : forall xs, P xs.
  Proof.
    assert (forall xs l : list A, List.length l <= List.length xs -> P l) as H_ind.
    { induction xs; intros l Hlen; apply H; intros l0 H0.
      - inversion Hlen. omega.
      - apply IHxs. simpl in Hlen. omega.
    }
    intros xs.
    apply H_ind with (xs := xs).
    omega.
  Qed.
End list_length_ind.


              
            


(*
Inductive symbol_det {g : grammar} :
  symbol -> Prop :=
| T_det :
  forall y word word' tr tr',
    (@derivesTree g) (T y) word tr
    -> (@derivesTree g) (T y) word' tr'
    -> word = word' /\ tr = tr'
    -> symbol_det (T y)
| NT_det :
    forall x,
      (forall gamma gamma' word f f',
          In (x, gamma) (productions g)
          -> In (x, gamma') (productions g)
          -> (@derivesForest g) gamma word f
          -> (@derivesForest g) gamma' word f'
          -> gamma = gamma' /\ f = f' /\ gamma_det gamma)
    -> symbol_det (NT x)
with gamma_det {g : grammar} :
       list symbol -> Prop :=
     | Fnil_det : gamma_det nil
     | Fcons_dfp :
         forall hd tl wpre wpre' wsuf wsuf' tr tr' f f',
           symbol_det hd
           -> gamma_det tl
           -> wpre ++ wsuf = wpre' ++ wsuf'
           -> (@derivesTree g) hd wpre tr
           -> (@derivesTree g) hd wpre' tr'
           -> (@derivesForest g) tl wsuf f
           -> (@derivesForest g) tl wsuf' f'
           -> wpre = wpre'
              /\ wsuf = wsuf'
              /\ tr = tr'
              /\ f = f'
           -> gamma_det (hd :: tl).
 *)

Scheme symbol_det_mutual_ind :=
  Induction for symbol_det Sort Prop
  with gamma_det_mutual_ind := Induction for gamma_det Sort Prop.

Inductive symbol_det' {g : grammar} :
  symbol -> Prop :=
| T_det' :
    forall y word word' tr tr',
      (@derivesTree g) (T y) word tr
      -> (@derivesTree g) (T y) word' tr'
      -> word = word' /\ tr = tr'
      -> symbol_det' (T y)
| NT_det' :
    forall x,
      (forall gamma gamma' word f f',
          In (x, gamma) (productions g)
          -> In (x, gamma') (productions g)
          -> (@derivesForest g) gamma word f
          -> (@derivesForest g) gamma' word f'
          -> gamma = gamma' /\ f = f')
      -> symbol_det' (NT x).


Definition symbol_det'' {g : grammar} sym :=
  forall word tr tr',
    (@derivesTree g) sym word tr
    -> (@derivesTree g) sym word tr'
    -> tr = tr'.


Lemma det_det' :
  forall g sym,
    (@symbol_det g) sym -> (@symbol_det' g) sym.
Proof.
  intros g sym.
  induction 1 using symbol_det_mutual_ind.
  - econstructor; eauto.
  - econstructor; intros.
    eapply a with (gamma := gamma) (f := f) in H2; eauto.
    destruct H2.
    destruct H3.
    split; auto.
Qed.

Lemma det'_det'' :
  forall g sym,
    (@symbol_det' g) sym -> (@symbol_det'' g) sym.
Proof.
  induction 1; intros.
  - unfold symbol_det''; intros.
    inv H2; inv H3; auto.
  - unfold symbol_det''; intros.
    inv H0; inv H1.
    eapply H with
        (gamma := gamma) (f := subtrees) in H5; eauto.
    destruct H5.
    subst; auto.
Qed.

Lemma det_det'' :
  forall g sym,
    (@symbol_det g) sym -> (@symbol_det'' g) sym.
Proof.
  intros.
  apply det'_det''.
  apply det_det'.
  auto.
Qed.

Lemma ll1_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym,
      (@derivesTree 
      (@symbol_det g) sym.
Proof.
  destruct sym

  
  induction sym.
  - admit.
  - 
  destruct sym as [y | x].
  - econstructor; eauto.
    + constructor.
    + constructor.
  - econstructor; intros.
    assert (gamma' = gamma) by admit; subst.
    induction gamma.
    + inv H2; inv H3.
      repeat (split; auto).
      constructor.
    + 
  

    
                
    
                    

Inductive symbol_dfp {g : grammar} :
  symbol -> Prop :=
| T_dfp :
  forall y wpre wpre' wsuf wsuf' tr tr',
    (@derivesTree g) (T y) wpre tr
    -> (@derivesTree g) (T y) wpre' tr'
    -> wpre ++ wsuf = wpre' ++ wsuf
    -> wpre = wpre' /\ wsuf = wsuf'
    -> symbol_dfp (T y)
| NT_dfp :
    forall x gamma,
      In (x, gamma) (productions g)
      -> gamma_dfp gamma
      -> symbol_dfp (NT x)
with gamma_dfp {g : grammar} :
       list symbol -> Prop :=
     | Fnil_dfp : gamma_dfp nil
     | Fcons_dfp :
         forall sym syms,
           symbol_dfp sym
           -> gamma_dfp syms
           -> gamma_dfp (sym :: syms).

Scheme symbol_dfp_ind' := Induction for symbol_dfp Sort Prop
  with gamma_dfp_ind' := Induction for gamma_dfp Sort Prop.

Lemma dfp :
  forall g sym,
    (@symbol_dfp g) sym
    -> forall x gpre gsuf wpre wpre' wsuf wsuf' tr tr'
              fsuf fsuf',
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesTree g) sym wpre tr
      -> (@derivesTree g) sym wpre' tr'
      -> (@derivesForest g) gsuf wsuf fsuf
      -> (@derivesForest g) gsuf wsuf' fsuf'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> wpre = wpre' /\ wsuf = wsuf'.
Proof.
  intros g sym.
  induction 1 using symbol_dfp_ind' with
      (P := fun sym (pf : symbol_dfp sym) =>
              forall x gpre gsuf wpre wpre' wsuf wsuf' tr tr'
                     fsuf fsuf',
                In (x, gpre ++ sym :: gsuf) (productions g)
                -> (@derivesTree g) sym wpre tr
                -> (@derivesTree g) sym wpre' tr'
                -> (@derivesForest g) gsuf wsuf fsuf
                -> (@derivesForest g) gsuf wsuf' fsuf'
                -> wpre ++ wsuf = wpre' ++ wsuf'
                -> wpre = wpre' /\ wsuf = wsuf')
      (P0 := fun gamma (pf : gamma_dfp gamma) =>
               forall wpre wpre' wsuf wsuf' f f',
                (@derivesForest g) gamma wpre f
                -> (@derivesForest g) gamma wpre' f'
                -> wpre ++ wsuf = wpre' ++ wsuf'
                -> wpre = wpre' /\ wsuf = wsuf'); intros.

  - inv H0; inv H1; inv H4.
    split; auto.

  - inv H0; inv H1.
    assert (gamma0 = gamma1) by admit.
    subst.
    inv g0.
    
  

Lemma dfp :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr x gpre sym gsuf wpre wsuf fsuf,
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesTree g) sym wpre tr
      -> (@derivesForest g) gsuf wsuf fsuf
      -> (@symbol_dfp g) sym.
Proof.
  intros tbl g Htbl.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall x gpre sym gsuf wpre wsuf fsuf,
                In (x, gpre ++ sym :: gsuf) (productions g)
                -> (@derivesTree g) sym wpre tr
                -> (@derivesForest g) gsuf wsuf fsuf
                -> (@symbol_dfp g) sym)
      (P0 := fun fsuf =>
               forall x gpre gsuf word,
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesForest g) gsuf word fsuf
                 -> (@gamma_dfp g) gsuf); intros.
  - inv H0.
    eapply T_dfp; constructor; auto.

  - inv H0.
    eapply NT_dfp; eauto.
    eapply IHtr with (gpre := nil); eauto.

  - inv H0.
    constructor.

  - inv H0.
    eapply Fcons_dfp; eauto.
    eapply IHtr0; eauto.
    assert (hdRoot :: tlRoots = [hdRoot] ++ tlRoots) by auto.
    rewrite H0 in H.
    rewrite app_assoc in H.
    eauto.
    Unshelve.
    auto.
Qed.
    
Definition treeDerivesFixedPrefix (g : grammar) (tr : tree) :=
  forall tr tr' sym wpre wpre' wsuf wsuf',
    (@derivesTree g) sym wpre tr
    -> (@derivesTree g) sym wpre' tr'
    -> wpre ++ wsuf = wpre' ++ wsuf'
    -> wpre = wpre'
       /\ wsuf = wsuf'
       /\ tr = tr'.

Definition forestDerivesFixedPrefix g f :=
  ForallF (treeDerivesFixedPrefix g) f.

Lemma ForallF_derivesForest :
  forall g f f' gamma wpre wpre' wsuf wsuf',
    forestDerivesFixedPrefix g f
    -> (@derivesForest g) gamma wpre f
    -> (@derivesForest g) gamma wpre' f'
    -> wpre ++ wsuf = wpre' ++ wsuf'
    -> wpre = wpre' /\ wsuf = wsuf' /\ f = f'.
Proof.
  induction f; intros.
  - inv H0; inv H1.
    simpl in *.
    repeat (split; auto).
  - inv H; inv H0; inv H1.
    eapply H5 with
        (wpre := prefix)
        (wpre' := prefix0)
        (wsuf := suffix ++ wsuf)
        (wsuf' := suffix0 ++ wsuf') in H3; eauto.
    (* Not sure why that didn't give me prefix = prefix0 *)
    + destruct H3.
      subst.
      eapply IHf in H10; eauto.
      destruct H10.
      destruct H1.
      subst.
      repeat apply prefixes_eq in H2; subst.
      repeat (split; auto).
    + repeat rewrite app_assoc. auto.
Qed.

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
      -> treeDerivesFixedPrefix g tr.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall x gpre gsuf word,
                 In (x, gpre ++ gsuf) (productions g)
                 -> derivesForest gsuf word fsuf
                 -> forestDerivesFixedPrefix g fsuf);
    intros.
  
  - inv H0; inv H1; inv H4.
    repeat (split; auto).

  - inv H0; inv H1.
    assert (gamma0 = gamma) by admit; subst.
    pose proof H9 as H9'.
    eapply IHtr with (gpre := nil) in H9; eauto.
    eapply ForallF_derivesForest in H9; eauto.
    destruct H9.
    destruct H1.
    subst.
    repeat (split; auto). 

  - constructor.

  - inv H0.
    constructor.
    + unfold derivesFixedPrefix; intros.
      

      eapply IHtr0 with
          (gpre := gpre ++ [hdRoot]) in H6; eauto.
      * unfold derivesFixedPrefix; intros.
        

      eapply IHtr in H6; eauto.
    + eapply IHtr0 with
          (gpre := gpre ++ [hdRoot]); eauto.
      assert (hdRoot :: tlRoots = [hdRoot] ++ tlRoots) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      eauto.
    constructor.
    + unfold derivesFixedPrefix; intros.
      destruct tr as [y | rx].
      * inv H0; inv H1; inv H2.
        repeat (split; auto).
      * inv H0.
        inv H5.
        inv H1.
        
      apply IHtr in 
    + eapply IHtr0 with
          (gpre := gpre ++ [hdRoot]); eauto.
      assert (hdRoot :: tlRoots = [hdRoot] ++ tlRoots) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      eauto.
      


    
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

Lemma or_thing :
  forall g tr tr' sym word,
    (@derivesTree g) sym word tr
    -> (@derivesTree g) sym word tr'
    -> tr = tr'
       \/ exists x gamma gamma' word' f f',
        In (x, gamma) (productions g)
        /\ In (x, gamma') (productions g)
        /\ (@derivesForest g) gamma word' f
        /\ (@derivesForest g) gamma' word' f'
        /\ gamma <> gamma'.
Proof.
  intro g.
  induction tr using tree_mutual_ind with
      (P := fun tr => 
              forall tr' sym word,
                (@derivesTree g) sym word tr
                -> (@derivesTree g) sym word tr'
                -> tr = tr'
                   \/ exists x gamma gamma' word' f f',
                    In (x, gamma) (productions g)
                    /\ In (x, gamma') (productions g)
                    /\ (@derivesForest g) gamma word' f
                    /\ (@derivesForest g) gamma' word' f'
                    /\ gamma <> gamma')
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesForest g) gamma word f
                 -> (@derivesForest g) gamma word f'
                 -> f = f'
                    \/ exists x gamma gamma' word' f f',
                     In (x, gamma) (productions g)
                     /\ In (x, gamma') (productions g)
                     /\ (@derivesForest g) gamma word' f
                     /\ (@derivesForest g) gamma' word' f'
                     /\ gamma <> gamma'); intros.
  - inv H; inv H0.
    left; auto.

  - inv H; inv H0.
    destruct (list_eq_dec symbol_eq_dec gamma0 gamma).
    + subst.
      apply IHtr in H2; auto.
      destruct H2.
      * subst.
        left; auto.
      * right.
        auto.
    + right.
      exists s; exists gamma; exists gamma0; exists word;
        exists f; exists subtrees.
      repeat (split; auto).

  - inv H; inv H0.
    left; auto.

  - inv H; inv H0.
    destruct (list_eq_dec string_dec prefix prefix0).
    + subst.
      apply suffixes_eq in H2.
      subst.
      apply IHtr in H3; auto.
Abort.

Lemma even_splits :
  forall tbl g,
    isParseTableFor tbl g
    -> forall wsuf gsuf x gpre wpre wpre' wsuf' fsuf fsuf',
      In (x, gpre ++ gsuf) (productions g)
      -> (@derivesForest g) gsuf wsuf fsuf
      -> (@derivesForest g) gsuf wsuf' fsuf'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> wpre = wpre'
         /\ wsuf = wsuf'.
Proof.
  intros tbl g Htbl.
  induction wsuf as [| stok stoks]; intros.
  - rewrite app_nil_r in *.
    subst.
    admit.
  - 
    
Abort.


(* IN THIS SECTION, I'M TRYING TO PROVE THAT AN LL(1) 
   DERIVATION TREE MUST SPLIT THE INPUT DETERMINISTICALLY,
   WITHOUT WORRYING ABOUT TREE STRUCTURE *)

Fixpoint size tr :=
  match tr with
  | Leaf _ => 0
  | Node _ f => S (sizeForest f)
  end
with sizeForest f :=
       match f with
       | Fnil => 0
       | Fcons tr f' => size tr + sizeForest f'
       end.

Lemma nat_strong_ind: forall (P:nat -> Prop),
P 0 -> (forall n:nat, (forall (m:nat), m <= n -> P m) -> P (S n)) -> forall n, P n.
Proof.
intros P B IHs n.
destruct n.
exact B.
apply IHs.
induction n.
intros m H; replace m with 0; try omega; exact B.
intros m H.
assert (m <= n \/ m = S n) as J; try omega.
destruct J as [J|J].
apply IHn; omega.
rewrite J.
apply IHs. 
apply IHn.
Qed.

Lemma length_nil: forall A:Type, forall l:list A, 
  l = nil <-> List.length l = 0.
Proof.
split; intros H.
rewrite H; simpl; auto.
destruct l. auto.
contradict H; simpl.
apply sym_not_eq; apply O_S.
Qed.

Lemma length_strong_ind: forall (A:Type) (P:list A -> Prop),
P nil -> (forall (n:nat) (k:list A), (forall (l:list A), List.length l <= n -> P l) -> List.length k = S n -> P k) -> forall l, P l.
Proof.
intros A P B IH.
assert (forall (n:nat) (l:list A), List.length l <= n -> P l) as G.
intro n.
induction n as [| n IHS] using nat_strong_ind.
intros l H.
assert (List.length l = 0) as G; try omega.
apply length_nil in G.
rewrite G; exact B.
intro l.
intro H.
assert (List.length l <= n \/ List.length l = S n) as G; try omega.
destruct G as [G|G].
apply IHS with (m:=n); auto.
apply IH with (n:=n); try exact G.
intro k.
apply IHS with (m:=n) (l:=k).
auto.
intro l.
apply G with (n:=List.length l); auto.
Qed.

(* EACH TREE/SYMBOL STRIPS AWAY JUST ONE PREFIX *)

Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall word tr tr' sym,
      (@derivesTree g) sym word tr
      -> (@derivesTree g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  intro word.
  induction word using length_strong_ind; intros.
  - destruct sym.
    + inv H.
    + inv H.
      inv H0.
      admit.
  - destruct sym.
    + inv H1; inv H2.
      auto.
    + inv H1.
      inv H2.
  
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesForest g) gamma word f
                 -> (@derivesForest g) gamma word f'
                 -> f = f'); intros.
  

(* Maybe do induction on wsuf *)
Lemma rosenkrantz_lemma_4'' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall word wmid lx gpre rx gamma gsuf
              wsuf
              fmid fsuf,
      In (lx, gpre ++ NT rx :: gsuf) (productions g)
      -> In (rx, gamma) (productions g)
      -> (@derivesForest g) gamma wmid fmid
      -> (@derivesForest g) gsuf wsuf fsuf
      -> forall wmid' wsuf' gamma' fmid' fsuf',
          In (rx, gamma') (productions g)
          -> (@derivesForest g) gamma' wmid' fmid'
          -> (@derivesForest g) gsuf wsuf' fsuf'
          -> word = wmid ++ wsuf
          -> word = wmid' ++ wsuf'
          -> wmid = wmid'
             /\ wsuf = wsuf'
             /\ gamma = gamma'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as H.
  destruct H as [Hmin Hcom].
  induction word as [| tok toks]; intros.
  - admit.
  - destruct wmid as [| mtok mtoks]; simpl in *; subst.
    + destruct wmid' as [| mtok' mtoks']; simpl in *; subst.
      * apply derivesForest_nil_nullable in H1.
        apply derivesForest_nil_nullable in H4.
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
      * (* first/follow conflict *)
        exfalso.
        inv H7.
        admit.
    + inv H7.
      destruct wmid' as [| mtok' mtoks'] eqn:Hwm; simpl in *.
      * (* another first/follow conflict *)
        admit.
      * inv H6.
        inv H9.
        
        inv H2; inv H5.
        
        eapply IHtoks with
            (gamma := gamma)
            (wmid := mtoks)
            (wsuf0 := wsuf)
            (wmid' := mtok' :: mtoks')
            (gamma' := gamma')
            (wsuf' := wsuf') in H5; eauto.
        assert (Hlk : (@isLookaheadFor g)
                        (LA mtok')
                        (NT rx)
                        gamma).
          { unfold isLookaheadFor.
            right.
            split.
            { constructor; auto.
              apply derivesForest_nil_nullable in H2.
              auto. }
            { constructor; auto.
              eapply FoRight; eauto.
              apply derivesForest_cons_firstGamma in H3.
              auto. }}
          assert (Hlk' : (@isLookaheadFor g)
                           (LA mtok')
                           (NT rx)
                           gamma').
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesForest_cons_firstGamma in H5.
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
            apply derivesForest_cons_firstGamma in H5.
            auto. }
          assert ((@nullableProd g) (NT rx) gamma').
          { constructor; auto.
            apply derivesForest_nil_nullable in H2.
            auto. }
          assert ((@followProd g)
                    (LA mtok')
                    (NT rx) gamma').
          { constructor; auto.
            econstructor; eauto.
            apply derivesForest_cons_firstGamma in H3.
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
          apply derivesForest_nil_nullable in H5.
          auto. }
        { constructor; auto.
          eapply FoRight; eauto.
          apply derivesForest_cons_firstGamma in H6.
          auto. }}
      assert (Hlk' : (@isLookaheadFor g)
                       (LA mtok)
                       (NT rx)
                       gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto.
        apply derivesForest_cons_firstGamma in H2.
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
        apply derivesForest_cons_firstGamma in H2.
        auto. }
      assert ((@nullableProd g) (NT rx) gamma').
      { constructor; auto.
        apply derivesForest_nil_nullable in H5.
        auto. }
      assert ((@followProd g)
                (LA mtok)
                (NT rx) gamma').
      { constructor; auto.
        econstructor; eauto.
        apply derivesForest_cons_firstGamma in H6.
        auto. }
      eapply no_first_follow_conflicts; eauto.
    + inv H7.
      inv H2.
      inv H5.
      subst.
      apply derivesForest_cons_firstGamma in H0.
      apply derivesForest_cons_firstGamma in Hderm.
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
      subst.
Qed.

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
               forall fsuf' x gpre gsuf
                      wpre wpre' wsuf wsuf',
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesForest g) gsuf wsuf fsuf
                 -> (@derivesForest g) gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf'); intros.

  - inv H; inv H0; auto.

  - inv H; inv H0.
    assert (gamma0 = gamma) by admit; subst.
    eapply IHtr with (gpre := nil) in H2; eauto.
    destruct H2.
    destruct H0.
    subst; auto.

  - inv H0; inv H1.
    repeat rewrite app_nil_r in *.
    repeat (split; auto).

  - inv H0; inv H1.
                     