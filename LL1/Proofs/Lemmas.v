Require Import List.

Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.

Require Import LL1.Derivation.
Require Import LL1.Parser.
Require Import LL1.ParseTable.

Import ListNotations.

Lemma pt_find_in :
  forall k A (v : A) m,
    ParseTable.find k m = Some v
    -> ParseTable.In k m.
Proof.
  intros.
  rewrite ParseTableFacts.in_find_iff.
  rewrite H; congruence.
Qed.

Lemma lookaheadmap_find_in : forall k vT (v : vT) m,
    LaMap.find k m = Some v ->
    LaMap.In k m.
Proof.
  intros. rewrite LaMapFacts.in_find_iff. rewrite H.
  unfold not. intro Hcontra. inv Hcontra.
Qed.

Lemma pt_lookup_in :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> ParseTable.In (x, la) tbl.
Proof.
  intros x la tbl gamma Hlkp.
  unfold pt_lookup in Hlkp.
  apply ParseTableFacts.in_find_iff; congruence.
Qed.

Lemma eof_first_sym :
  forall g la sym,
    first_sym g la sym
    -> la = EOF
    -> False.
Proof.
  induction 1; intros; auto.
  inv H.
Qed.

Lemma eof_first_gamma :
  forall g la gamma,
    first_gamma g la gamma
    -> la = EOF
    -> False.
Proof.
  intros.
  inv H.
  eapply eof_first_sym; eauto.
Qed.

Lemma nullable_middle_sym :
  forall g xs ys sym,
    nullable_gamma g (xs ++ sym :: ys)
    -> nullable_sym g sym.
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
    nullable_gamma g (xs ++ T y :: zs)
    -> False.
Proof.
  induction xs; intros.
  - simpl in H.
    inv H.
    inv H2.
  - destruct a.
    + inv H.
      inv H2.
    + inv H.
      eapply IHxs; eauto.
Qed.

Lemma nullable_split :
  forall g xs ys,
    nullable_gamma g (xs ++ ys)
    -> nullable_gamma g ys.
Proof.
  induction xs; intros.
  - auto.
  - inv H.
    eapply IHxs; eauto.
Qed.

(* New version, without mutual induction *)
Lemma no_first_follow_conflicts :
  forall tbl g,
    parse_table_for tbl g
    -> forall la sym,
      first_sym g la sym
      -> nullable_sym g sym
      -> follow_sym g la sym
      -> False.
Proof.
  intros tbl g Htbl la sym Hfi.
  induction Hfi; intros.
  - inv H.
  - inv H1.
    assert (ys = gpre ++ s :: gsuf).
    { destruct Htbl as [Hmin Hcom].
      assert (Hlk : lookahead_for la x (gpre ++ s :: gsuf) g).
      { unfold lookahead_for; auto. }
      assert (Hlk' : lookahead_for la x ys g).
      { unfold lookahead_for; auto. }
      unfold pt_complete in Hcom.
      apply Hcom in Hlk; auto.
      apply Hcom in Hlk'; auto.
      congruence. }
    subst.
    eapply IHHfi.
    + apply nullable_middle_sym in H5; auto.
    + destruct s.
      * apply gamma_with_terminal_not_nullable in H5; inv H5.
      * eapply FollowLeft; eauto.
        assert (NT n :: gsuf = [NT n] ++ gsuf) by auto.
        rewrite H1 in H5.
        rewrite app_assoc in H5.
        apply nullable_split in H5.
        auto.
Qed.

Lemma sym_derives_nil_nullable :
  forall g sym wpre f wsuf,
    (@sym_derives_prefix g) sym wpre f wsuf
    -> wpre = nil
    -> nullable_sym g sym.
Proof.
  intros g sym wpre f wsuf Hder.
  induction Hder using sdp_mutual_ind with
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix sym wpre tr wsuf) =>
              wpre = nil
              -> nullable_sym g sym)
      (P0 := fun gamma wpre f wsuf
                 (pf : gamma_derives_prefix gamma wpre f wsuf)
             =>
               wpre = nil
               -> nullable_gamma g gamma); intros; subst.
  - inv H.
  - simpl in *.
    econstructor; eauto.
  - constructor.
  - apply app_eq_nil in H; destruct H; subst.
    destruct IHHder; auto.
    constructor; auto.
    econstructor; eauto.
Qed.

Lemma gamma_derives_cons_first_gamma :
  forall g gamma word f rem,
    (@gamma_derives_prefix g) gamma word f rem
    -> forall tok toks,
      word = tok :: toks
      -> first_gamma g (LA tok) gamma.
Proof.
  intros g gamma word f rem Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym word tr rem
                (pf : sym_derives_prefix sym word tr rem) =>
              forall tok toks,
                word = tok :: toks
                -> first_sym g (LA tok) sym)
      (P0 := fun gamma word f rem
                 (pf : gamma_derives_prefix gamma word f rem)
             =>
               forall tok toks,
                 word = tok :: toks
                 -> first_gamma g (LA tok) gamma); intros; subst.
  - inv H; constructor.
  - simpl in *.
    specialize (IHHder tok toks).
    destruct IHHder; auto.
    econstructor; eauto.
  - inv H.
  - destruct hdRoot.
    + inv s.
      inv H.
      eapply FirstGamma with (gpre := nil); constructor.
    + destruct wpre as [| ptok ptoks]; simpl in *.
      * subst.
        specialize (IHHder0 tok toks).
        destruct IHHder0; auto.
        eapply FirstGamma with (gpre := NT n :: gpre).
        -- constructor; auto.
           apply sym_derives_nil_nullable in s; auto.
        -- auto.
      * inv H.
        eapply FirstGamma with (gpre := nil).
        -- constructor.
        -- eapply IHHder; eauto.
Qed.

Lemma parse_t_ret_leaf :
  forall tbl y input fuel tree suffix,
    parse tbl (T y) input fuel = (Some tree, suffix) ->
    isLeaf tree = true.
Proof.
  intros. destruct fuel.
  - inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (Utils.beqString y s).
      * inv H. reflexivity.
      * inv H.
Qed.

Lemma parse_nt_ret_node :
  forall tbl x input fuel tree suffix,
    parse tbl (NT x) input fuel = (Some tree, suffix)
    -> isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct (pt_lookup x (peek input) tbl).
    + destruct (parseForest tbl l input fuel). 
      destruct o. 
      * inv H. trivial.
      * inv H.
    + inv H. 
Qed.

Lemma tbl_entry_is_lookahead :
  forall tbl g x la gamma,
    parse_table_for tbl g
    -> pt_lookup x la tbl = Some gamma
    -> lookahead_for la x gamma g.
Proof.
  intros tbl g x la gamma Htbl Hlkp.
  destruct Htbl as [Hsou Hcom].
  unfold pt_sound in Hsou.
  apply Hsou; auto.
Qed.

Lemma first_gamma_first_sym :
  forall g x la gamma,
    In (x, gamma) g.(productions)
    -> first_gamma g la gamma
    -> first_sym g la (NT x).
Proof.
  intros g x la gamma Hin Hfg.
  inv Hfg.
  econstructor; eauto.
Qed.

