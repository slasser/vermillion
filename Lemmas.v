Require Import Bool FMaps List Omega String MSets.
Require Import Grammar Tactics.
Open Scope list_scope.

Module LemmasFn (Import G : Grammar.T).
  
  Lemma find_In : forall k vT (v : vT) m,
      NtMap.find k m = Some v ->
      NtMap.In k m.
  Proof.
    intros. rewrite NtMapFacts.in_find_iff. rewrite H.
    unfold not. intro Hcontra. inv Hcontra.
  Qed.
  
  Lemma ntmap_find_in : forall k vT (v : vT) m,
      NtMap.find k m = Some v ->
      NtMap.In k m.
  Proof.
    intros. rewrite NtMapFacts.in_find_iff. rewrite H.
    unfold not. intro Hcontra. inv Hcontra.
  Qed.
  
  Ltac copy_and_find_In H :=
    let Hfind := fresh "Hfind" in
    let Heq   := fresh "Heq" in 
    remember H as Hfind eqn:Heq; clear Heq;
    apply find_In in H.
  
  Lemma T_not_in_NT_list :
    forall (gamma : list symbol) (y : terminal),
      forallb isNT gamma = true ->
      ~In (T y) gamma.
  Proof.
    intro gamma.
    induction gamma; unfold not; simpl; intros.
    - assumption.
    - apply andb_true_iff in H. destruct H.
      destruct H0.
      + rewrite H0 in H. inv H.
      + apply IHgamma with (y := y) in H1.
        apply H1. apply H0.
  Qed.
  
  (* Some useful lemmas to remember : in_eq, in_cons *)
  Lemma NT_list_neq_list_with_T :
    forall (gamma prefix suffix : list symbol)
           (y : terminal),
      forallb isNT gamma = true ->
      gamma <> (prefix ++ T y :: suffix)%list.
  Proof.
    unfold not. intros.
    apply T_not_in_NT_list with (y := y) in H.
    apply H. clear H.
    rewrite H0. rewrite in_app_iff.
    right. apply in_eq.
  Qed.
  
  Lemma NT_not_in_T_list :
    forall (gamma : list symbol) (X : nonterminal),
      forallb isT gamma = true ->
      ~In (NT X) gamma.
  Proof.
    intro gamma.
    induction gamma; unfold not; simpl; intros.
    - assumption.
    - apply andb_true_iff in H. destruct H.
      destruct H0.
      + rewrite H0 in H. inv H.
      + apply IHgamma with (X := X) in H1.
        apply H1. assumption.
  Qed.
  
  Lemma T_list_neq_list_with_NT :
    forall (gamma prefix suffix : list symbol)
           (X : nonterminal),
      forallb isT gamma = true ->
      gamma <> (prefix ++ NT X :: suffix)%list.
  Proof.
    unfold not; intros.
    apply NT_not_in_T_list with (X := X) in H.
    apply H; clear H.
    rewrite H0. rewrite in_app_iff.
    right. apply in_eq.
  Qed.

  Lemma pt_find_in :
  forall k A (v : A) m,
    ParseTable.find k m = Some v
    -> ParseTable.In k m.
Proof.
  intros.
  rewrite ParseTableFacts.in_find_iff.
  rewrite H; congruence.
Qed.

(*
Lemma lookaheadmap_find_in : forall k vT (v : vT) m,
    LaMap.find k m = Some v ->
    LaMap.In k m.
Proof.
  intros. rewrite LaMapFacts.in_find_iff. rewrite H.
  unfold not. intro Hcontra. inv Hcontra.
Qed.
*)
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
    parse_table_correct tbl g
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
      eapply Hcom in Hlk; eauto.
      eapply Hcom in Hlk'; eauto.
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
    sym_derives_prefix g sym wpre f wsuf
    -> wpre = nil
    -> nullable_sym g sym.
Proof.
  intros g sym wpre f wsuf Hder.
  induction Hder using sdp_mutual_ind with
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix g sym wpre tr wsuf) =>
              wpre = nil
              -> nullable_sym g sym)
      (P0 := fun gamma wpre f wsuf
                 (pf : gamma_derives_prefix g gamma wpre f wsuf)
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
    gamma_derives_prefix g gamma word f rem
    -> forall t v toks,
      word = (existT _ t v) :: toks
      -> first_gamma g (LA t) gamma.
Proof.
  intros g gamma word f rem Hder.
  induction Hder using gdp_mutual_ind with
      (P := fun sym word tr rem
                (pf : sym_derives_prefix g sym word tr rem) =>
              forall t v toks,
                word = (existT _ t v) :: toks
                -> first_sym g (LA t) sym)
      (P0 := fun gamma word f rem
                 (pf : gamma_derives_prefix g gamma word f rem)
             =>
               forall t v toks,
                 word = (existT _ t v) :: toks
                 -> first_gamma g (LA t) gamma); intros; subst.
  - inv H; constructor.
  - simpl in *.
    specialize (IHHder t v toks).
    destruct IHHder; auto.
    econstructor; eauto.
  - inv H.
  - destruct s.
    + inv s0.
      inv H.
      eapply FirstGamma with (gpre := nil); constructor.
    + destruct wpre as [| ptok ptoks]; simpl in *.
      * subst.
        specialize (IHHder0 t v0 toks).
        destruct IHHder0; auto.
        eapply FirstGamma with (gpre := NT n :: gpre).
        -- constructor; auto.
           apply sym_derives_nil_nullable in s0; auto.
        -- auto.
      * inv H.
        eapply FirstGamma with (gpre := nil).
        -- constructor.
        -- eapply IHHder; eauto.
Qed.

Lemma tbl_entry_is_lookahead :
  forall tbl g x x' la gamma f,
    parse_table_correct tbl g
    -> pt_lookup x la tbl = Some (existT _ (x', gamma) f)
    -> lookahead_for la x gamma g.
Proof.
  intros tbl g x x' la gamma f Htbl Hlkp.
  destruct Htbl as [Hsou Hcom].
  unfold pt_sound in Hsou.
  apply Hsou in Hlkp; destruct Hlkp as [Heq [Hin Hl]]; subst; auto.
Qed.

Lemma first_gamma_first_sym :
  forall g x la gamma f,
    In (existT _ (x, gamma) f) g.(prods)
    -> first_gamma g la gamma
    -> first_sym g la (NT x).
Proof.
  intros g x la gamma f Hin Hfg.
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
  forall (k : ParseTable.key) (A : Type) (a : A) (l : list (ParseTable.key * A)),
    findA (ParseTableFacts.eqb k) l = Some a
    -> In (k, a) l.
Proof.
  intros k A a l Hf.
  induction l as [| p l' IHl].
  - inv Hf.
  - simpl in *.
    destruct p as (k', gamma').
    destruct (ParseTableFacts.eqb k k') eqn:Heq.
    + inv Hf.
      unfold ParseTableFacts.eqb in *.
      destruct (ParseTableFacts.eq_dec k k').
      * subst; auto.
      * inv Heq.
    + right; auto.
Defined.
      
Lemma pt_lookup_elements :
  forall x la tbl p,
    pt_lookup x la tbl = Some p
    -> In ((x, la), p) (ParseTable.elements tbl).
Proof.
  intros.
  unfold pt_lookup in *.
  rewrite ParseTableFacts.elements_o in H.
  apply pt_lookup_elements'; auto.
Defined.

  Lemma cons_app_singleton :
    forall A (x : A) (ys : list A),
      x :: ys = [x] ++ ys.
  Proof.
    auto.
  Defined.

  Lemma in_app_cons :
    forall A (x : A) (pre suf : list A),
      In x (pre ++ x :: suf).
  Proof.
    intros A x pre suf.
    induction pre; simpl; auto.
  Defined.

  (* alternative FirstGamma definition that simplifies
     reasoning in some cases *)
  Inductive first_gamma' (g : grammar) (la : lookahead) :
    list symbol -> Prop :=
  | FG_hd : forall h t,
      first_sym g la h
      -> first_gamma' g la (h :: t)
  | FG_tl : forall h t,
      nullable_sym g h
      -> first_gamma' g la t
      -> first_gamma' g la (h :: t).

  Lemma first_gamma_iff_first_gamma' :
    forall g la gamma,
      first_gamma g la gamma <-> first_gamma' g la gamma.
  Proof.
    intros g la gamma; split; intros H.
    - inv H.
      revert H0.
      revert H1.
      revert s gsuf.
      induction gpre; intros; simpl in *.
      + constructor; auto.
      + inv H0.
        apply FG_tl; auto.
    - induction H.
      + rewrite <- app_nil_l.
        constructor; auto.
      + inv IHfirst_gamma'.
        apply FirstGamma with (gpre := h :: gpre)
                              (s := s)
                              (gsuf := gsuf); auto.
  Qed.

  Lemma medial :
    forall A pre pre' (sym sym' : A) suf suf',
      pre ++ sym :: suf = pre' ++ sym' :: suf'
      -> In sym pre' \/ In sym' pre \/ pre = pre' /\ sym = sym' /\ suf = suf'.
  Proof.
    induction pre; intros; simpl in *.
    - destruct pre' eqn:Hp; simpl in *.
      + inv H; auto.
      + inv H; auto.
    - destruct pre' eqn:Hp; subst; simpl in *.
      + inv H; auto.
      + inv H.
        apply IHpre in H2.
        destruct H2; auto.
        repeat destruct H; auto.
  Qed.

  Lemma nullable_sym_in :
    forall g sym gamma,
      nullable_gamma g gamma
      -> In sym gamma
      -> nullable_sym g sym.
  Proof.
    intros.
    induction gamma.
    - inv H0.
    - inv H.
      inv H0; auto.
  Qed.

  Lemma first_gamma_split :
    forall g la xs ys,
      first_gamma g la ys
      -> nullable_gamma g xs
      -> first_gamma g la (xs ++ ys).
  Proof.
    induction xs; intros; simpl in *; auto.
    inv H0.
    apply first_gamma_iff_first_gamma'.
    apply FG_tl; auto.
    apply first_gamma_iff_first_gamma'; auto.
  Qed.

  Lemma app_assoc_under_rhs_semty :
    forall xs ys zs,
      rhs_semty (xs ++ ys ++ zs) = rhs_semty ((xs ++ ys) ++ zs).
  Proof.
    intros xs; induction xs as [| x xs' IHxs]; intros ys zs; simpl in *; auto.
    unfold rhs_semty in *; simpl in *.
    rewrite IHxs; auto.
  Qed.

  Lemma rhss_eq_exists_prod' :
    forall g x gamma gamma' f,
      In (existT action_ty (x, gamma) f) g.(prods)
      -> gamma = gamma'
      -> exists f',
          In (existT action_ty (x, gamma') f') g.(prods).
  Proof.
    intros; simpl in *; subst; eauto.
  Qed.

  Lemma follow_pre :
    forall g x la sym suf pre f,
      In (existT _ (x, pre ++ suf) f) g.(prods)
      -> In sym pre
      -> nullable_gamma g pre
      -> first_gamma g la suf
      -> follow_sym g la sym.
  Proof.
    intros g x la sym suf pre f Hin Hin' Hng Hfg.
    apply in_split in Hin'.
    destruct Hin' as [l1 [l2 Heq]]; subst.
    destruct sym.
    - exfalso.
      eapply gamma_with_terminal_not_nullable; eauto. 
    - apply rhss_eq_exists_prod' with
          (gamma' := l1 ++ NT n :: (l2 ++ suf))
        in Hin.
      + destruct Hin as [f' Hin]; simpl in Hin.
        eapply FollowRight with (x1 := x)
                                (gpre := l1)
                                (gsuf := l2 ++ suf); eauto.
        apply nullable_split in Hng; inv Hng.
        apply first_gamma_split; auto.
      + rewrite <- app_assoc; auto.
  Qed.

  Lemma first_sym_rhs_eqs :
    forall g t,
      parse_table_correct t g
      -> forall x pre pre' sym sym' suf suf' f f' la,
        In (existT _ (x, pre ++ sym :: suf) f) g.(prods)
        -> In (existT _ (x, pre' ++ sym' :: suf') f') g.(prods)
        -> nullable_gamma g pre
        -> nullable_gamma g pre'
        -> first_sym g la sym
        -> first_sym g la sym'
        -> pre = pre' /\ sym = sym' /\ suf = suf'.
  Proof.
    intros g t Ht x pre pre' sym sym' suf suf' f f' la Hi Hi' Hn Hn' Hf Hf'.
    assert (Heq: pre ++ sym :: suf = pre' ++ sym' :: suf').
    { assert (Hl : lookahead_for la x (pre ++ sym :: suf) g).
      { left; eauto. }
      assert (Hl' : lookahead_for la x (pre' ++ sym' :: suf') g).
      { left; eauto. }
      eapply Ht in Hl; eapply Ht in Hl'; eauto.
      rewrite Hl in Hl'; inv Hl'; auto. }
    apply medial in Heq.
    destruct Heq as [Hin | [Hin' | Heq]]; auto.
    - exfalso; eapply no_first_follow_conflicts with (sym := sym); eauto.
      + eapply nullable_sym_in; eauto.
      + eapply follow_pre; eauto.
        apply FirstGamma with (gpre := []); eauto.
    - exfalso; eapply no_first_follow_conflicts with (sym := sym'); eauto.
      + eapply nullable_sym_in with (gamma := pre); eauto.
      + eapply follow_pre with (pre := pre); eauto.
        apply FirstGamma with (gpre := []); auto.
  Qed.

  Lemma lookups_eq :
    forall x la t xp xp',
      pt_lookup x la t = Some xp
      -> pt_lookup x la t = Some xp'
      -> xp = xp'.
  Proof.
    intros; tc.
  Qed.

  Lemma production_eq_dec :
    forall (p p' : production),
      {p = p'} + {p <> p'}.
  Proof.
    repeat decide equality.
  Defined.

  Lemma in_xprods_in_prodsOf :
    forall g p f,
      In (existT _ p f) g.(prods)
      -> In p (prodsOf g).
  Proof.
    intros g p f Hin.
    unfold prodsOf. unfold prodOf.
    induction g.(prods) as [| xp xps]; simpl in *; inv Hin; auto.
  Qed.

  Lemma in_prodsOf_exists_in_xprods :
    forall g p,
      In p (prodsOf g)
      -> exists f, In (existT _ p f) g.(prods).
  Proof.
    unfold prodsOf; unfold prodOf; intros g (x, gamma) Hin.
    induction g.(prods) as [| [(x', gamma') f] xps]; simpl in *; inv Hin.
    - inv H; eauto.
    - apply IHxps in H; destruct H as [f' Hin]; eauto.
  Qed.
  
End LemmasFn.

