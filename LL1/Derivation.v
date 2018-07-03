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
      (@lookahead_for g) (peek (word ++ rem)) (NT x) gamma
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
    (@first_gamma g) la gamma
    -> la = EOF
    -> False.
Proof.
  intros g la gamma H.
  induction H using first_gamma_mutual_ind with
      (P := fun la x gamma (pf : first_prod la x gamma) =>
              la = EOF -> False)
      (P0 := fun la gamma (pf : first_gamma la gamma) =>
               la = EOF -> False)
      (P1 := fun la sym (pf : first_sym la sym) =>
               la = EOF -> False); intros.
  - apply IHfirst_gamma; trivial.
  - apply IHfirst_gamma; trivial.
  - apply IHfirst_gamma; trivial. 
  - inv H.
  - apply IHfirst_gamma; trivial.
Qed.

Lemma nullable_middle_sym :
  forall g xs ys sym,
    (@nullable_gamma g) (xs ++ sym :: ys)
    -> (@nullable_sym g) sym.
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
    (@nullable_gamma g) (xs ++ T y :: zs)
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
    (@nullable_gamma g) (xs ++ ys)
    -> (@nullable_gamma g) ys.
Proof.
  induction xs; intros.
  - auto.
  - inv H.
    eapply IHxs; eauto.
Qed.

Lemma no_first_follow_conflicts :
  forall tbl g,
    parse_table_for tbl g
    -> forall la sym,
      (@first_sym g) la sym
      -> (@nullable_sym g) sym
      -> (@follow_sym g) la sym
      -> False.
Proof.
  intros tbl g Htbl la sym Hfi.
  destruct Htbl as [Hmin Hcom].
  induction Hfi using first_sym_mutual_ind with
      (P := fun la sym gamma
                (pf : (@first_prod g) la sym gamma) =>
              (@nullable_prod g) sym gamma
              -> (@follow_sym g) la sym 
              -> False)
      (P0 := fun la gammaSuf
                 (pf : (@first_gamma g) la gammaSuf) =>
               forall sym gammaPre,
                 (@first_prod g) la sym (gammaPre ++ gammaSuf)
                 -> (@nullable_prod g) sym (gammaPre ++ gammaSuf)
                 -> (@follow_sym g) la sym
                 -> False)
      (P1 := fun la sym (pf : (@first_sym g) la sym) =>
              (@nullable_sym g) sym
              -> (@follow_sym g) la sym
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
    assert (Hlk : (@lookahead_for g) la (NT x) gamma).
    { unfold lookahead_for.
      left.
      auto. }
    assert (Hlk' : (@lookahead_for g) la (NT x) ys).
    { unfold lookahead_for.
      right.
      split.
      { constructor; auto. }
      { constructor; auto. }}
    unfold pt_complete in Hcom.
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
    (@lookahead_for g) la (NT x) gamma
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
    -> (@nullable_gamma g) gamma.
Proof.
  intros g gamma wpre f wsuf Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix sym wpre tr wsuf) =>
              wpre = nil
              -> nullable_sym sym)
      (P0 := fun gamma wpre f wsuf
                 (pf : gamma_derives_prefix gamma wpre f wsuf)
             =>
               wpre = nil
               -> nullable_gamma gamma); intros; subst.
  - inv H.
(*  - inv f; simpl in *.
    eapply eof_fgamma in H2; eauto; inv H2. *)
  - econstructor.
    econstructor; eauto.
    apply lookahead_in_grammar in l; auto.
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
      -> (@first_gamma g) (LA tok) gamma.
Proof.
  intros g gamma word f rem Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym word tr rem
                (pf : sym_derives_prefix sym word tr rem) =>
              forall tok toks,
                word = tok :: toks
                -> first_sym (LA tok) sym)
      (P0 := fun gamma word f rem
                 (pf : gamma_derives_prefix gamma word f rem)
             =>
               forall tok toks,
                 word = tok :: toks
                 -> first_gamma (LA tok) gamma); intros; subst.
  - inv H; constructor.
  - simpl in *.
    apply lookahead_in_grammar in l.
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
    parse_table_for tbl g
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
    { destruct l as [Hfi | Hfo].
      - destruct H2 as [Hfi' | Hfo'].
        + rewrite <- H0 in Hfi'.
          destruct Htbl as [Hmin Hcom].
          unfold pt_complete in Hcom.
          assert ((@lookahead_for g) (peek (word ++ rem))
                                       (NT x)
                                       gamma).
           { left; auto. }
           assert ((@lookahead_for g) (peek (word ++ rem))
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
          unfold pt_complete in Hcom.
          rewrite <- H0 in H4.
          assert ((@lookahead_for g) (peek (word ++ rem))
                                       (NT x)
                                       gamma).
          { right; split; auto. }
           assert ((@lookahead_for g) (peek (word ++ rem))
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
