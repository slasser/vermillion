Require Import FMaps List.

Require Import Grammar.
Require Import ParseTree.
Require Import Tactics.

Require Import Derivation.
Require Import ParseTable.
Require Import ParseTableGen.

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
  forall g gpre y gsuf,
    ~ nullable_gamma g (gpre ++ T y :: gsuf).
Proof.
  unfold not.
  induction gpre as [| sym syms]; intros y gsuf Hnu; simpl in *.
  - inv Hnu.
    inv H1.
  - destruct sym.
    + inv Hnu.
      inv H1.
    + inv Hnu.
      eapply IHsyms; eauto.
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

Lemma in_A_not_in_B_in_diff :
  forall elt a b,
    NtSet.In elt a
    -> ~ NtSet.In elt b
    -> NtSet.In elt (NtSet.diff a b).
Proof.
  ND.fsetdec.
Defined.

Lemma in_list_iff_in_fromNtList :
  forall x l, In x l <-> NtSet.In x (fromNtList l).
Proof.
  split; intros; induction l; simpl in *.
  - inv H.
  - destruct H; subst; auto.
    + ND.fsetdec.
    + apply IHl in H; ND.fsetdec.
  - ND.fsetdec.
  - destruct (NtSetFacts.eq_dec x a); subst; auto.
    right. apply IHl. ND.fsetdec.
Defined.

Lemma pt_lookup_elements' :
  forall (k : ParseTable.key) (gamma : list symbol) (l : list (ParseTable.key * list symbol)),
    findA (ParseTableFacts.eqb k) l = Some gamma
    -> In (k, gamma) l.
Proof.
  intros.
  induction l.
  - inv H.
  - simpl in *.
    destruct a as (k', gamma').
    destruct (ParseTableFacts.eqb k k') eqn:Heq.
    + inv H.
      unfold ParseTableFacts.eqb in *.
      destruct (ParseTableFacts.eq_dec k k').
      * subst; auto.
      * inv Heq.
    + right; auto.
Defined.
      
Lemma pt_lookup_elements :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> In ((x, la), gamma) (ParseTable.elements tbl).
Proof.
  intros.
  unfold pt_lookup in *.
  rewrite ParseTableFacts.elements_o in H.
  apply pt_lookup_elements'; auto.
Defined.