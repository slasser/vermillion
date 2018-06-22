Require Import List String.
Require Import Grammar LL1.Parser ParseTree ParseTable
        Lib.Tactics.
Import ListNotations.
Open Scope list_scope.

Inductive sym_derives_prefix {g : grammar} :
  symbol -> list string -> tree -> list string -> Prop :=
| T_sdp : 
    forall (y : string) (rem : list string),
      sym_derives_prefix (T y) [y] (Leaf y) rem
| NT_sdp :
    forall (x : string) 
           (gamma : list symbol)
           (word rem : list string) 
           (subtrees : list tree),
      (@isLookaheadFor g) (peek (word ++ rem)) (NT x) gamma
      -> gamma_derives_prefix gamma word subtrees rem
      -> sym_derives_prefix (NT x) word (Node x subtrees) rem
with gamma_derives_prefix {g : grammar} : 
       list symbol -> list string -> list tree -> list string -> Prop :=
     | Nil_gdp : forall rem,
         gamma_derives_prefix [] [] [] rem
     | Cons_gdp : 
         forall (hdRoot : symbol)
                (wpre wsuf rem : list string)
                (hdTree : tree)
                (tlRoots : list symbol)
                (tlTrees : list tree),
         sym_derives_prefix hdRoot wpre hdTree (wsuf ++ rem)
         -> gamma_derives_prefix tlRoots wsuf tlTrees rem
         -> gamma_derives_prefix (hdRoot :: tlRoots) 
                                 (wpre ++ wsuf)
                                 (hdTree :: tlTrees)
                                 rem.

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

Lemma lookahead_in_grammar :
  forall g la x gamma,
    (@isLookaheadFor g) la (NT x) gamma
    -> In (x, gamma) (productions g).
Proof.
  intros.
  destruct H as [Hfi | Hfo].
  - inv Hfi; auto.
  - destruct Hfo.
    inv H; auto.
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
(*  - inv f; simpl in *.
    eapply eof_fgamma in H2; eauto; inv H2. *)
  - econstructor.
    econstructor; eauto.
    apply lookahead_in_grammar in i; auto.
  - constructor.
  - apply app_eq_nil in H; destruct H; subst.
    destruct hdRoot as [y | x].
    + inv s.
    + econstructor; eauto.
Qed.

Lemma gamma_derives_cons_fg :
  forall g gamma word f rem,
    (@gamma_derives_prefix g) gamma word f rem
    -> forall tok toks,
      word = tok :: toks
      -> (@firstGamma g) (LA tok) gamma.
Proof.
  intros g gamma word f rem Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym word tr rem
                (pf : sym_derives_prefix sym word tr rem) =>
              forall tok toks,
                word = tok :: toks
                -> firstSym (LA tok) sym)
      (P0 := fun gamma word f rem
                 (pf : gamma_derives_prefix gamma word f rem)
             =>
               forall tok toks,
                 word = tok :: toks
                 -> firstGamma (LA tok) gamma); intros; subst.
  - inv H; constructor.
  - simpl in *.
    apply lookahead_in_grammar in i.
    econstructor.
    econstructor; eauto.
  - inv H.
  - destruct hdRoot.
    + inv s.
      inv H.
      constructor.
      constructor.
    + destruct wpre as [| ptok ptoks]; simpl in *.
      * eapply FiGammaTl.
        -- inv s; simpl in *.
           apply lookahead_in_grammar in H1.
           econstructor.
           econstructor; eauto.
           eapply gamma_derives_nil_nullable; eauto.
        -- eapply IHHder0; eauto.
      * inv H.
        eapply FiGammaHd.
        eapply IHHder; eauto.
Qed.
        
Lemma der_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym word rem tr,
      (@sym_derives_prefix g) sym word tr rem
      -> forall word' rem' tr',
        (@sym_derives_prefix g) sym word' tr' rem'
        -> word ++ rem = word' ++ rem'
        -> word = word' /\ rem = rem' /\ tr = tr'.
Proof.
  intros tbl g Htbl sym word rem tr Hder.
  induction Hder using sdp_mutual_ind with
      (P := fun sym word tr rem
                (pf : sym_derives_prefix
                        sym word tr rem) =>
              forall word' rem' tr',
                sym_derives_prefix sym word' tr' rem'
                -> word ++ rem = word' ++ rem'
                -> word = word' /\ rem = rem' /\ tr = tr')
      (P0 := fun gamma word f rem
                 (pf : gamma_derives_prefix gamma word f rem) =>
               forall word' rem' f',
                 gamma_derives_prefix gamma word' f' rem'
                 -> word ++ rem = word' ++ rem'              
                 -> word = word' /\ rem = rem' /\ f = f'); intros.
  - inv H; inv H0; auto.
    
  - (* Nt case *)
    inv H.
    assert (gamma0 = gamma).
    { destruct i as [Hfi | Hfo].
      - destruct H2 as [Hfi' | Hfo'].
        + rewrite <- H0 in Hfi'.
          destruct Htbl as [Hmin Hcom].
          unfold ptComplete in Hcom.
          assert ((@isLookaheadFor g) (peek (word ++ rem))
                                       (NT x)
                                       gamma).
           { left; auto. }
           assert ((@isLookaheadFor g) (peek (word ++ rem))
                                       (NT x)
                                       gamma0).
           { left; auto. }
           apply Hcom in H.
           apply Hcom in H1.
           destruct H as [m [Hs Hl]].
           destruct H1 as [m' [Hs' Hl']].
           congruence.
        + exfalso.
          destruct Hfo'.
          eapply no_first_follow_conflicts with (sym := NT x); eauto.
          * econstructor; eauto.
          * econstructor; eauto.
          * inv H1.
            rewrite H0.
            auto.
      - destruct H2 as [Hfi' | Hfo'].
        + exfalso.
          destruct Hfo.
          eapply no_first_follow_conflicts with (sym := NT x); eauto.
           * econstructor; eauto.
           * econstructor; eauto.
           * inv H1.
             rewrite <- H0.
             auto.
        + destruct Hfo; destruct Hfo'.
          destruct Htbl as [Hmin Hcom].
          unfold ptComplete in Hcom.
          rewrite <- H0 in H4.
          assert ((@isLookaheadFor g) (peek (word ++ rem))
                                       (NT x)
                                       gamma).
          { right; split; auto. }
           assert ((@isLookaheadFor g) (peek (word ++ rem))
                                       (NT x)
                                       gamma0).
          { right; split; auto. }
          apply Hcom in H5.
          apply Hcom in H6.
          destruct H5 as [m [Hs Hl]].
          destruct H6 as [m' [Hs' Hl']].
          congruence. }
    subst.
    eapply IHHder in H3; eauto.
    destruct H3.
    destruct H1.
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
Qed.
