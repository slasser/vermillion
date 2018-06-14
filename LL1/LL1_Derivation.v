Require Import List String.
Require Import Grammar LL1.Parser ParseTree ParseTable
        Lib.Tactics.
Import ListNotations.
Open Scope list_scope.

(* "symbol Sym derives input prefix Pre, producing tree Tr
    and leaving input suffix Suf unconsumed *)
Inductive sym_derives_prefix {g : grammar} :
  symbol -> list string -> tree -> list string -> Prop :=
| T_sdp : 
    forall (y : string) (wsuf : list string),
      sym_derives_prefix (T y) [y] (Leaf y) wsuf
| NtFirst_sdp :
    forall (x : string) 
           (gamma : list symbol)
           (wpre wsuf : list string) 
           (subtrees : forest),
      (@firstProd g) (peek wpre) (NT x) gamma
      -> gamma_derives_prefix gamma wpre subtrees wsuf
      -> sym_derives_prefix (NT x) wpre (Node x subtrees) wsuf
| NtFollow_sdp :
    forall (x : string) 
           (gamma : list symbol)
           (wsuf : list string) 
           (subtrees : forest),
      (@followProd g) (peek wsuf) (NT x) gamma
      -> gamma_derives_prefix gamma [] subtrees wsuf
      -> sym_derives_prefix (NT x) [] (Node x subtrees) wsuf
with gamma_derives_prefix {g : grammar} : 
       list symbol -> list string -> forest -> list string -> Prop :=
     | Nil_gdp : forall wsuf,
         gamma_derives_prefix [] [] Fnil wsuf
     | Cons_gdp : 
         forall (hdRoot : symbol)
                (wpre wmid wsuf : list string)
                (hdTree : tree)
                (tlRoots : list symbol)
                (tlTrees : forest),
         sym_derives_prefix hdRoot wpre hdTree (wmid ++ wsuf)
         -> gamma_derives_prefix tlRoots wmid tlTrees wsuf
         -> gamma_derives_prefix (hdRoot :: tlRoots) 
                                 (wpre ++ wmid)
                                 (Fcons hdTree tlTrees)
                                 wsuf.
            (* Incorrect statement I had before :
                   gamma_derives_prefix (hdRoots :: tlRoots)
                                        wpre
                                        (Fcons hdTree tlTrees)
                                        (wpre ++ wmid)
            *)

Scheme sdp_mutual_ind :=
  Induction for sym_derives_prefix Sort Prop
  with gdp_mutual_ind :=
    Induction for gamma_derives_prefix Sort Prop.

Lemma eof_fgamma :
  forall g la gamma,
    (@firstGamma g) la gamma
    -> la = EOF
    -> False.
Proof.
  intros g la gamma H.
  induction H using firstGamma_mutual_ind with
      (P := fun la x gamma (pf : firstProd la x gamma) =>
              la = EOF -> False)
      (P0 := fun la gamma (pf : firstGamma la gamma) =>
               la = EOF -> False)
      (P1 := fun la sym (pf : firstSym la sym) =>
               la = EOF -> False); intros.
  - apply IHfirstGamma; trivial.
  - apply IHfirstGamma; trivial.
  - apply IHfirstGamma; trivial. 
  - inv H.
  - apply IHfirstGamma; trivial.
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
    -> forall la sym,
      (@firstSym g) la sym
      -> (@nullableSym g) sym
      -> (@followSym g) la sym
      -> False.
Proof.
  intros tbl g Htbl la sym Hfi.
  destruct Htbl as [Hmin Hcom].
  induction Hfi using firstSym_mutual_ind with
      (P := fun la sym gamma
                (pf : (@firstProd g) la sym gamma) =>
              (@nullableProd g) sym gamma
              -> (@followSym g) la sym 
              -> False)
      (P0 := fun la gammaSuf
                 (pf : (@firstGamma g) la gammaSuf) =>
               forall sym gammaPre,
                 (@firstProd g) la sym (gammaPre ++ gammaSuf)
                 -> (@nullableProd g) sym (gammaPre ++ gammaSuf)
                 -> (@followSym g) la sym
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

  - intros sym gammaPre Hfi' Hnu Hfo.
    eapply IHHfi.
    + inv Hnu.
      apply nullable_middle_sym in H0.
      auto.
    + destruct hd.
      * inv Hnu.
        apply gamma_with_terminal_not_nullable in H0.
        inv H0.
      * inv Hnu.
        eapply FoLeft; eauto.
        assert (NT n :: tl = [NT n] ++ tl) by auto.
        rewrite H1 in H0.
        rewrite app_assoc in H0.
        eapply nullable_split in H0.
        auto.        

  - intros sym gammaPre Hfi Hnu Hfo.
    eapply IHHfi; eauto.
    + assert (NT x :: tl = [NT x] ++ tl) by auto.
      rewrite H in Hfi.
      rewrite app_assoc in Hfi.
      eauto.
    + rewrite <- app_assoc.
      simpl.
      auto.

  - intros Hnu Hfo.
    inv Hfo.

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
    + auto.
Qed.

Lemma gamma_derives_nil_nullable :
  forall g gamma wpre f wsuf,
    (@gamma_derives_prefix g) gamma wpre f wsuf
    -> wpre = nil
    -> (@nullableGamma g) gamma.
Proof.
  intros g gamma wpre f wsuf Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix sym wpre tr wsuf) =>
              wpre = nil
              -> nullableSym sym)
      (P0 := fun gamma wpre f wsuf
                 (pf : gamma_derives_prefix gamma wpre f wsuf)
             =>
               wpre = nil
               -> nullableGamma gamma); intros; subst.
  - inv H.
  - inv f; simpl in *.
    eapply eof_fgamma in H2; eauto; inv H2.
  - inv f.
    econstructor.
    econstructor; eauto.
  - constructor.
  - apply app_eq_nil in H; destruct H; subst.
    destruct hdRoot as [y | x].
    + inv s.
    + econstructor; eauto.
Qed.

Lemma der_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym wpre wsuf tr,
      (@sym_derives_prefix g) sym wpre tr wsuf
      -> forall wpre' wsuf' tr',
        (@sym_derives_prefix g) sym wpre' tr' wsuf'
        -> wpre ++ wsuf = wpre' ++ wsuf'
        -> wpre = wpre' /\ wsuf = wsuf' /\ tr = tr'.
Proof.
  intros tbl g Htbl sym wpre wsuf tr Hder.
  induction Hder using sdp_mutual_ind with
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix
                        sym wpre tr wsuf) =>
              forall wpre' wsuf' tr',
                sym_derives_prefix sym wpre' tr' wsuf'
                -> wpre ++ wsuf = wpre' ++ wsuf'
                -> wpre = wpre' /\ wsuf = wsuf' /\ tr = tr')
      (P0 := fun gamma wpre f wsuf
                 (pf : gamma_derives_prefix gamma wpre f wsuf) =>
               forall wpre' wsuf' f',
                 gamma_derives_prefix gamma wpre' f' wsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'              
                 -> wpre = wpre' /\ wsuf = wsuf' /\ f = f'); intros.
  - inv H; inv H0; auto.
    
  - (* NtFirst case *)
    inv H.
    + destruct wpre as [| ptok ptoks]; simpl in *.
      * inv f.
        eapply eof_fgamma in H5; eauto; inv H5.
      * destruct wpre' as [| ptok' ptoks']; simpl in *.
        -- inv H2.
           eapply eof_fgamma in H5; eauto; inv H5.
        -- inv H0.
           assert (gamma0 = gamma).
           { destruct Htbl as [Hmin Hcom].
             unfold ptComplete in Hcom.
             assert ((@isLookaheadFor g) (LA ptok')
                                         (NT x)
                                         gamma).
             { unfold isLookaheadFor; auto. }
             assert ((@isLookaheadFor g) (LA ptok')
                                         (NT x)
                                         gamma0).
             { unfold isLookaheadFor; auto. }
             apply Hcom in H.
             destruct H as [m [Hs Hl]].
             apply Hcom in H0.
             destruct H0 as [m' [Hs' Hl']].
             congruence. }
           subst.
           eapply IHHder in H3; eauto.
           ++ destruct H3.
              destruct H0.
              subst.
              apply app_inv_tail in H4.
              auto.
           ++ rewrite <- app_comm_cons.
              rewrite H4.
              auto.
    + destruct wpre as [| ptok ptoks]; simpl in *.
      * inv f.
        eapply eof_fgamma in H5; eauto; inv H5.
      * destruct wsuf' as [| stok' stoks']; simpl in *.
        -- inv H0.
        -- inv H0.
           assert ((@firstSym g) (LA stok') (NT x)) by
               (econstructor; eauto).
           assert ((@nullableSym g) (NT x)).
           {  inv H2.
             econstructor.
             econstructor; eauto.
             eapply gamma_derives_nil_nullable in H3; eauto. }
           assert ((@followSym g) (LA stok') (NT x)).
           { inv H2; auto. }
           eapply no_first_follow_conflicts in H; eauto.
           inv H.
  - (* NtFollow case *)
    simpl in *.
    inv H; simpl in *.
    + destruct wpre' as [| ptok' ptoks']; simpl in *.
      * inv H2.
        eapply eof_fgamma in H4; eauto; inv H4.
      * assert ((@firstSym g) (LA ptok') (NT x)) by
               (econstructor; eauto).
        assert ((@nullableSym g) (NT x)).
        { inv f.
          econstructor.
          econstructor; eauto.
          eapply gamma_derives_nil_nullable in g0; eauto. }
        assert ((@followSym g) (LA ptok') (NT x)).
        { inv f; auto. }
        eapply no_first_follow_conflicts in H; eauto.
        inv H.
    + assert (gamma0 = gamma).
      { destruct Htbl as [Hmin Hcom].
        unfold ptComplete in Hcom.
        assert ((@isLookaheadFor g) (peek wsuf')
                                    (NT x)
                                    gamma).
        { unfold isLookaheadFor.
          right.
          split.
          - inv f.
            constructor; auto.
            eapply gamma_derives_nil_nullable in g0; eauto.
          - auto. }
        assert ((@isLookaheadFor g) (peek wsuf')
                                    (NT x)
                                    gamma0).
        { unfold isLookaheadFor.
          right.
          split.
          - inv H2.
            constructor; auto.
            eapply gamma_derives_nil_nullable in H3; eauto.
          - auto. }
        apply Hcom in H.
        destruct H as [m [Hs Hl]].
        apply Hcom in H0.
        destruct H0 as [m' [Hs' Hl']].
        congruence. }
      subst.
      eapply IHHder in H3; eauto.
      destruct H3.
      destruct H0.
      subst; auto.

  - inv H; auto.

  - inv H.
    eapply IHHder in H3; eauto.
    + destruct H3.
      destruct H1; subst.
      eapply IHHder0 in H7; eauto.
      destruct H7.
      destruct H2.
      subst; auto.
    + repeat rewrite app_assoc; auto.
Qed. (* Finally! *)            

    