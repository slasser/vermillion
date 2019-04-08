Require Import List.
Require Import Omega.
Require Import String.
Require Import Wf_nat.
Require Import Grammar.
Require Import Tactics.
Require Import Lemmas.
Require Import Generator.
Require Import Parser.
Require Import Parser_sound.
Import ListNotations.
Open Scope list_scope.

Module ParserSafetyFn (Import G : Grammar.T).

  Module Export ParserSoundness := ParserSoundnessFn G.
  Module Import L := LemmasFn G.

  Inductive nullable_path g (la : lookahead) :
    symbol -> symbol -> Prop :=
  | DirectPath : forall x z gamma pre suf,
      In (x, gamma) g.(prods)
      -> gamma = pre ++ NT z :: suf
      -> nullable_gamma g pre
      -> lookahead_for la x gamma g
      -> nullable_path g la (NT x) (NT z)
  | IndirectPath : forall x y z gamma pre suf,
      In (x, gamma) g.(prods)
      -> gamma = pre ++ NT y :: suf
      -> nullable_gamma g pre
      -> lookahead_for la x gamma g
      -> nullable_path g la (NT y) (NT z)
      -> nullable_path g la (NT x) (NT z).

  Hint Constructors nullable_path.

  Definition left_recursive g sym la :=
    nullable_path g la sym sym.

  Inductive sized_first_sym (g : grammar) : lookahead -> symbol -> nat -> Prop :=
  | SzFirstT  : forall y : terminal, sized_first_sym g (LA y) (T y) 0
  | SzFirstNT : forall (x : nonterminal) (gpre : list symbol)
                       (s : symbol) (gsuf : list symbol)
                       (la : lookahead) (n : nat),
      In (x, gpre ++ s :: gsuf) g.(prods)
      -> nullable_gamma g gpre
      -> sized_first_sym g la s n
      -> sized_first_sym g la (NT x) (S n).

  Hint Constructors sized_first_sym.

  Lemma first_sym_exists_size :
    forall g la sym,
      first_sym g la sym
      -> exists n, sized_first_sym g la sym n.
  Proof.
    intros.
    induction H.
    - exists 0.
      constructor.
    - destruct IHfirst_sym as [n Hf].
      eexists.
      econstructor; eauto.
  Qed.

  Lemma sized_fs_fs :
    forall g la sym n,
      sized_first_sym g la sym n
      -> first_sym g la sym.
  Proof.
    intros g la sym n Hf; induction Hf; auto.
    econstructor; eauto.
  Qed.

  Lemma sized_first_sym_det :
    forall g t la sym n,
      parse_table_correct t g
      -> sized_first_sym g la sym n
      -> forall n',
          sized_first_sym g la sym n'
          -> n = n'.
  Proof.
    intros g t la sym n Ht Hf.
    induction Hf as [y | x pre sym suf la n Hi Hn Hf IH]; intros n' Hf'; inv Hf'; auto.
    pose proof Hf as Hf'; pose proof H3 as H3'.
    apply sized_fs_fs in Hf; apply sized_fs_fs in H3.
    eapply first_sym_rhs_eqs in Hf; eauto.
    destruct Hf as [He [He' He'']]; subst.
    erewrite IH; eauto.
  Qed.

  Lemma sized_first_sym_np :
    forall g la x y,
      nullable_path g la x y
      -> first_sym g la y
      -> exists nx ny,
          sized_first_sym g la x nx
          /\ sized_first_sym g la y ny
          /\ ny < nx.
  Proof.
    intros g la x y Hn.
    induction Hn; intros; subst.
    - apply first_sym_exists_size in H3.
      destruct H3.
      assert (sized_first_sym g la (NT x) (S x0)).
      { econstructor; eauto. }
      exists (S x0); exists x0; split; auto.
    - apply IHHn in H3.
      destruct H3 as [nx [ny [Hf [Hf' Hlt]]]].
      assert (sized_first_sym g la (NT x) (S nx)).
      { econstructor; eauto. }
      exists (S nx); exists ny; split; auto.
  Qed.

  Inductive sized_nullable_sym (g : grammar) : symbol -> nat -> Prop :=
  | SzNullableSym : forall (x : nonterminal)
                           (ys : list symbol)
                           (n : nat),
      In (x, ys) g.(prods)
      -> sized_nullable_gamma g ys n
      -> sized_nullable_sym g (NT x) (S n)
  with sized_nullable_gamma (g : grammar) : list symbol -> nat -> Prop :=
       | SzNullableNil : sized_nullable_gamma g [] 0
       | SzNullableCons : forall (hd : symbol) (tl : list symbol)(n n' : nat),
           sized_nullable_sym g hd n
           -> sized_nullable_gamma g tl n'
           -> sized_nullable_gamma g (hd :: tl) (n + n').

  Hint Constructors sized_nullable_sym sized_nullable_gamma.

  Scheme sized_nullable_sym_mutual_ind := Induction for sized_nullable_sym Sort Prop
    with sized_nullable_gamma_mutual_ind := Induction for sized_nullable_gamma Sort Prop.

  Lemma sized_ns_ns :
    forall g sym n,
      sized_nullable_sym g sym n
      -> nullable_sym g sym.
  Proof.
    intros.
    induction H using sized_nullable_sym_mutual_ind with
        (P := fun sym n (H : sized_nullable_sym g sym n) =>
                nullable_sym g sym)
        (P0 := fun gamma n (H : sized_nullable_gamma g gamma n) =>
                 nullable_gamma g gamma).
    - econstructor; eauto.
    - constructor.
    - econstructor; eauto.
  Qed.

  Lemma sized_ng_ng :
    forall g gamma n,
      sized_nullable_gamma g gamma n
      -> nullable_gamma g gamma.
  Proof.
    intros.
    induction H using sized_nullable_gamma_mutual_ind with
        (P := fun sym n (H : sized_nullable_sym g sym n) =>
                nullable_sym g sym)
        (P0 := fun gamma n (H : sized_nullable_gamma g gamma n) =>
                 nullable_gamma g gamma); intros; econstructor; eauto.
  Qed.
  
  Lemma sized_nullable_sym_det :
    forall g t la sym n,
      parse_table_correct t g
      -> sized_nullable_sym g sym n
      -> follow_sym g la sym
      -> forall n',
          sized_nullable_sym g sym n'
          -> n = n'.
  Proof.
    intros g t la sym n Ht Hs.
    induction Hs using sized_nullable_sym_mutual_ind with
        (P := fun sym n (H : sized_nullable_sym g sym n) =>
                follow_sym g la sym
                -> forall n', sized_nullable_sym g sym n' -> n = n')
        (P0 := fun gsuf n (H : sized_nullable_gamma g gsuf n) =>
                 forall x gpre n',
                   In (x, gpre ++ gsuf) g.(prods)
                   -> follow_sym g la (NT x)
                   -> sized_nullable_gamma g gsuf n' -> n = n').

    - intros Hf n' Hs.
      inv Hs.
      assert (ys = ys0).
      { assert (lookahead_for la x ys g).
        { right.
          split; auto.
          apply sized_ng_ng in s; auto. }
        assert (lookahead_for la x ys0 g).
        { right; split; auto.
          apply sized_ng_ng in H1; auto. }
        apply Ht in H; auto.
        apply Ht in H2; auto.
        congruence. }
      subst.
      eapply IHHs with (gpre := nil) in Hf; eauto.
    - intros.
      inv H1.
      auto.
    - intros.
      inv H1.
      assert (follow_sym g la hd).
      { destruct hd as [y | x'].
        - inv H4.
        - eapply FollowLeft; eauto.
          apply sized_ng_ng in H6; auto. }
      apply IHHs in H4; auto; subst.
      eapply IHHs0 with (gpre := gpre ++ [hd]) in H6; eauto.
      rewrite <- app_assoc; auto.
  Qed.

  Lemma sized_ns_ex :
    forall g sym,
      nullable_sym g sym
      -> exists n, sized_nullable_sym g sym n.
  Proof.
    intros.
    induction H using nullable_sym_mutual_ind with
        (P := fun sym (H : nullable_sym g sym) =>
                exists n, sized_nullable_sym g sym n)
        (P0 := fun gamma (H : nullable_gamma g gamma) =>
                 exists n, sized_nullable_gamma g gamma n).
    - destruct IHnullable_sym.
      eexists; econstructor; eauto.
    - eexists; constructor; eauto.
    - destruct IHnullable_sym; destruct IHnullable_sym0.
      eexists; econstructor; eauto.
  Qed.

  Lemma sized_ng_ex :
    forall g gamma,
      nullable_gamma g gamma
      -> exists n, sized_nullable_gamma g gamma n.
  Proof.
    intros.
    induction H using nullable_gamma_mutual_ind with
        (P := fun sym (H : nullable_sym g sym) =>
                exists n, sized_nullable_sym g sym n)
        (P0 := fun gamma (H : nullable_gamma g gamma) =>
                 exists n, sized_nullable_gamma g gamma n).
    - destruct IHnullable_gamma.
      eexists; econstructor; eauto.
    - eexists; constructor; eauto.
    - destruct IHnullable_gamma; destruct IHnullable_gamma0.
      eexists; econstructor; eauto.
  Qed.

  Lemma sym_in_gamma_size_le :
    forall g gamma,
      nullable_gamma g gamma
      -> forall sym,
        In sym gamma
        -> exists n n',
          sized_nullable_sym g sym n
          /\ sized_nullable_gamma g gamma n'
          /\ n <= n'.
  Proof.
    intros g gamma.
    induction gamma; intros.
    - inv H0.
    - inv H.
      inv H0.
      + apply sized_ns_ex in H3.
        destruct H3.
        apply sized_ng_ex in H4.
        destruct H4.
        exists x; exists (x + x0); repeat split; auto.
        omega.
      + apply IHgamma in H; auto.
        destruct H as [n [n' [Hs [Hs' Hle]]]].
        apply sized_ns_ex in H3.
        destruct H3.
        exists n.
        exists (x + n').
        repeat split; auto.
        omega.
  Qed.

  Lemma sized_ns_np :
    forall g x y pre suf,
      In (x, pre ++ NT y :: suf) g.(prods)
      -> nullable_gamma g (pre ++ NT y :: suf)
      -> nullable_sym g (NT y)
      -> exists nx ny,
          sized_nullable_sym g (NT x) nx
          /\ sized_nullable_sym g (NT y) ny
          /\ ny < nx.
  Proof.
    intros.
    eapply sym_in_gamma_size_le with (sym := NT y) in H0; eauto.
    - destruct H0 as [n [n' [Hs [Hs' Hle]]]].
      exists (S n').
      exists n.
      repeat split; auto.
      + econstructor; eauto.
      + omega.
    - apply in_app_cons.
  Qed.

  Lemma exist_decreasing_nullable_sym_sizes_in_null_path :
    forall g t la x y,
      parse_table_correct t g
      -> nullable_sym g x 
      -> follow_sym g la x
      -> nullable_path g la x y
      -> exists nx ny,
          sized_nullable_sym g x nx
          /\ sized_nullable_sym g y ny
          /\ ny < nx.
  Proof.
    intros g t la x y Ht Hn Hf Hnp.
    induction Hnp as [x y gamma pre suf Hi He Hng Hl | x y z gamma pre suf Hi Heq Hng Hl Hnp IH]; intros; subst.
    - inv Hn.
      destruct Hl as [Hfg | [Hng' Hfo]].
      + (* LEMMA *)
        exfalso; eapply no_first_follow_conflicts with (sym := NT x); eauto.
        apply first_gamma_first_sym with (gamma := pre ++ NT y :: suf); auto.
      + eapply sized_ns_np; eauto.
        eapply nullable_middle_sym; eauto.
    - destruct Hl as [Hfg | [Hng' Hfo]].
      + exfalso; eapply no_first_follow_conflicts with (sym := NT x); eauto.
        apply first_gamma_first_sym with (gamma := pre ++ NT y :: suf); auto.
      + assert (Hn' : nullable_sym g (NT y)).
        { eapply nullable_middle_sym; eauto. }
        assert (Hfo' : follow_sym g la (NT y)).
        { eapply FollowLeft; eauto.
          eapply nullable_split with (xs := pre ++ [NT y]).
          rewrite <- app_assoc; auto. }
        apply IH in Hn'; clear IH; auto.
        destruct Hn' as [ny [nz [Hsy [Hsz Hlt]]]].
        eapply sized_ns_np in Hi; eauto.
        * destruct Hi as [nx [ny' [Hsx [Hsy' Hlt']]]].
          exists nx; exists nz; repeat (split; eauto).
          eapply sized_nullable_sym_det in Hsy'; eauto.
          omega.
        * eapply nullable_middle_sym; eauto.
  Qed.

  Lemma nullable_path_exists_production :
    forall g la x y,
      nullable_path g la (NT x) y
      -> exists gamma,
        In (x, gamma) g.(prods)
        /\ lookahead_for la x gamma g.
  Proof.
    intros g la x y Hn; inv Hn; eauto.
  Qed.

  Lemma LL1_parse_table_impl_no_left_recursion :
    forall g t la x,
      parse_table_correct t g
      -> ~ left_recursive g (NT x) la.
  Proof.
    intros g t la x Ht; unfold not; intros Hlr; red in Hlr.
    assert (Hex : exists gamma,
               In (x, gamma) g.(prods)
               /\ lookahead_for la x gamma g).
    { apply nullable_path_exists_production in Hlr; auto. }
    destruct Hex as [gamma [Hi Hl]].
    destruct Hl as [Hfg | [Hng Hfo]].
    - assert (Hf : first_sym g la (NT x)) by (inv Hfg; eauto).
      eapply sized_first_sym_np in Hf; eauto.
      destruct Hf as [n [n' [Hf [Hf' Hlt]]]].
      eapply sized_first_sym_det in Hf; eauto.
      omega.
    - assert (Hns : nullable_sym g (NT x)) by eauto.
      eapply exist_decreasing_nullable_sym_sizes_in_null_path in Hns; eauto.
      destruct Hns as [n [n' [Hs [Hs' Hlt]]]].
      eapply sized_nullable_sym_det in Hs; eauto.
      omega.
  Qed.

  Definition sa_size (sa : sym_arg) : nat :=
    match sa with
    | F_arg _ => 0
    | G_arg gamma => 1 + List.length gamma
    end.

  Lemma leftrec_conditions :
    forall g tbl,
      parse_table_correct tbl g
      -> forall (input : list terminal)
                (vis : NtSet.t)
                (sa : sym_arg),
        match sa with
        | F_arg sym =>
          forall a x vis' input',
            parseTree tbl sym input vis a = inl (LeftRec x vis' input')
            -> (NtSet.In x vis
                /\ (sym = NT x
                    \/ nullable_path g (peek input) sym (NT x)))
               \/ exists la, (left_recursive g (NT x) la)
        | G_arg gamma =>
          forall a x vis' input',
            parseForest_nf tbl gamma input vis a = inl (LeftRec x vis' input')
            -> (exists pre sym suf,
                   gamma = pre ++ sym :: suf
                   /\ nullable_gamma g pre
                   /\ NtSet.In x vis
                   /\ (sym = NT x
                       \/ nullable_path g (peek input) sym (NT x)))
               \/ exists la, (left_recursive g (NT x) la)
        end.
  Proof.
    intros g tbl Ht input.

    remember (List.length input) as l.
    generalize dependent input.
    induction l as [l IHl] using lt_wf_ind.
    intros input Hl; subst.

    intros vis.
    remember (NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl)) vis)) as card.
    generalize dependent vis.
    induction card as [card IHcard] using lt_wf_ind.
    intros vis Hcard; subst.

    intros sa.
    remember (sa_size sa) as sz.
    generalize dependent sa.
    induction sz as [sz IHsz] using lt_wf_ind.
    intros sa Hsa; subst.
    destruct sa.

    - (* sa = F_arg sym *)
      intros a x vis' input' Hp; destruct a.
      step.
      + step; tc.
        step; tc.
      + step; tc.
        destruct s as [gamma Hlk].
        step.
        * (* x is in vis *)
          inv Hp.
          left; split; auto.
        *  (* x is not in vis *)
          step_eq Hpf.
          -- inv Hp.
             eapply IHcard with (sa := G_arg gamma) in Hpf; eauto.
             clear IHl; clear IHsz; clear IHcard.
             destruct Hpf as [Hex | Hex].
             ++ destruct Hex as [pre [sym [suf [Hg [Hng [Hin Hrest]]]]]]; subst.
                rename x into x'; rename n into x.
                destruct Hrest as [Hin' | Hnin].
                ** subst.
                   destruct (NtSetFacts.eq_dec x x').
                   --- subst.
                       right.
                       exists (peek input).
                       red.
                       apply Ht in Hlk.
                       destruct Hlk.
                       eapply DirectPath with (pre := pre); eauto.
                   --- left.
                       split.
                       +++ ND.fsetdec.
                       +++ right.
                           apply Ht in Hlk.
                           destruct Hlk.
                           eapply DirectPath; eauto.
                ** destruct (NtSetFacts.eq_dec x x').
                   --- subst.
                       right.
                       exists (peek input).
                       red.
                       destruct sym as [y | z].
                       +++ inv Hnin.
                       +++ apply Ht in Hlk; destruct Hlk.
                           eapply IndirectPath with (y := z); eauto.
                   --- left.
                       split.
                       +++ ND.fsetdec.
                       +++ right.
                           destruct sym.
                           *** inv Hnin.
                           *** apply Ht in Hlk; destruct Hlk.
                               eapply IndirectPath with (y := n1); eauto.
             ++ right; auto.
             ++ apply NP.subset_cardinal_lt with (x := n); try ND.fsetdec.
                apply in_A_not_in_B_in_diff; auto.
                apply in_list_iff_in_fromNtList.
                eapply pt_lookup_in_nt_keys; eauto.
          -- step.
             step; tc.

    - intros a x vis' input' Hpf; destruct a.
      step; tc.
      step_eq Hpf.
      + (* calling parse on s returns LeftRec *)
        inv Hpf.
        eapply IHsz with (sa := F_arg s) (m := sa_size (F_arg s)) in Hpf0; eauto.
        * destruct Hpf0; auto.
          left.
          exists nil; exists s; exists l; split; auto. 
        * simpl; omega.
      + (* calling parse on s succeeds, calling parseForest on l returns LeftRec *)
        step.
        step.
        step.
        * (* parse consumed some input *)
          step_eq Hpf.
          -- inv Hpf.
             eapply IHl with (sa := G_arg l) in Hpf1; eauto.
             destruct Hpf1.
             ++ destruct H as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]].
                ND.fsetdec.
             ++ right; auto. 
          -- step.
             step; tc.
        * (* parse consumed no input *)
          subst.
          step_eq Hpf.
          inv Hpf.
          eapply IHsz with (sa := G_arg l) in Hpf1; eauto.
          destruct Hpf1.
          -- destruct H as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]]; subst.
             left.
             exists (s :: pre); exists sym; exists suf.
             repeat split; auto.
             eapply input_length_invariant in Hpf0; eauto.
             destruct Hpf0; try omega.
             econstructor; eauto.
          -- right; auto.
          -- step.
             step; tc.
  Qed.

End ParserSafetyFn.