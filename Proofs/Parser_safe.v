Require Import List.
Require Import Omega.
Require Import String.
Require Import Wf_nat.
Require Import Grammar.
Require Import Tactics.
Require Import Lemmas.
Require Import Parser.
Require Import Parser_sound.
Import ListNotations.
Open Scope list_scope.

Module ParserSafetyFn (Import G : Grammar.T).

  Module Export ParserSoundness := ParserSoundnessFn G.
  Module Import L := LemmasFn G.

  Inductive nullable_path (g : grammar) (la : lookahead) :
    symbol -> symbol -> Prop :=
  | DirectPath : forall x z gamma f pre suf,
      In (existT _ (x, gamma) f) g.(prods)
      -> gamma = pre ++ NT z :: suf
      -> nullable_gamma g pre
      -> lookahead_for la x gamma g
      -> nullable_path g la (NT x) (NT z)
  | IndirectPath : forall x y z gamma f pre suf,
      In (existT _ (x, gamma) f) g.(prods)
      -> gamma = pre ++ NT y :: suf
      -> nullable_gamma g pre
      -> lookahead_for la x gamma g
      -> nullable_path g la (NT y) (NT z)
      -> nullable_path g la (NT x) (NT z).

  Hint Constructors nullable_path.

  Definition left_recursive g sym la :=
    nullable_path g la sym sym.

  Inductive sized_first_sym (g : grammar) : lookahead -> symbol -> nat -> Prop :=
  | SzFirstT  : forall y, sized_first_sym g (LA y) (T y) 0
  | SzFirstNT : forall x gpre s gsuf f la n,
      In (existT _ (x, gpre ++ s :: gsuf) f) g.(prods)
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
    induction Hf as [y | x pre sym suf f la n Hi Hn Hf IH]; intros n' Hf'; inv Hf'; auto.
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
  | SzNullableSym : forall x gamma f n,
      In (existT _ (x, gamma) f) g.(prods)
      -> sized_nullable_gamma g gamma n
      -> sized_nullable_sym g (NT x) (S n)
  with sized_nullable_gamma (g : grammar) : list symbol -> nat -> Prop :=
       | SzNullableNil : sized_nullable_gamma g [] 0
       | SzNullableCons : forall s ss n n',
           sized_nullable_sym g s n
           -> sized_nullable_gamma g ss n'
           -> sized_nullable_gamma g (s :: ss) (n + n').
  
  Hint Constructors sized_nullable_sym sized_nullable_gamma.

  Scheme sized_ns_mutual_ind := Induction for sized_nullable_sym Sort Prop
    with sized_ng_mutual_ind := Induction for sized_nullable_gamma Sort Prop.

  Lemma sized_ns_ns :
    forall g sym n,
      sized_nullable_sym g sym n
      -> nullable_sym g sym.
  Proof.
    intros.
    induction H using sized_ns_mutual_ind with
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
    induction H using sized_ng_mutual_ind with
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
    induction Hs using sized_ns_mutual_ind with
        (P := fun sym n (H : sized_nullable_sym g sym n) =>
                follow_sym g la sym
                -> forall n',
                  sized_nullable_sym g sym n'
                  -> n = n')
        (P0 := fun gsuf n (H : sized_nullable_gamma g gsuf n) =>
                 forall x gpre f n',
                   In (existT _ (x, gpre ++ gsuf) f) g.(prods)
                   -> follow_sym g la (NT x)
                   -> sized_nullable_gamma g gsuf n'
                   -> n = n').

    - intros Hf n' Hs.
      inv Hs.
      assert (gamma = gamma0).
      { assert (lookahead_for la x gamma g).
        { right.
          split; auto.
          apply sized_ng_ng in s; auto. }
        assert (lookahead_for la x gamma0 g).
        { right; split; auto.
          apply sized_ng_ng in H1; auto. }
        eapply Ht in H; eauto.
        eapply Ht in H2; eauto.
        congruence. }
      subst.
      eapply IHHs with (gpre := nil) in Hf; eauto.
    - intros.
      inv H1.
      auto.
    - intros.
      inv H1.
      assert (follow_sym g la s).
      { destruct s as [y | x'].
        - inv H4.
        - eapply FollowLeft; eauto.
          apply sized_ng_ng in H6; auto. }
      apply IHHs in H4; auto; subst.
      apply rhss_eq_exists_prod' with
          (gamma' := (gpre ++ [s]) ++ ss) in H.
      + destruct H as [f' Hin].
        eapply IHHs0 with (gpre := gpre ++ [s]) in H6; eauto.
      + rewrite <- app_assoc; auto.        
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
    forall g x y pre suf f,
      In (existT _ (x, pre ++ NT y :: suf) f) g.(prods)
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
    induction Hnp as [x y gamma f pre suf Hi He Hng Hl |
                      x y z gamma f pre suf Hi Heq Hng Hl Hnp IH]; intros; subst.
    - inv Hn.
      destruct Hl as [Hfg | [Hng' Hfo]].
      + (* LEMMA *)
        exfalso; eapply no_first_follow_conflicts with (sym := NT x); eauto.
        eapply first_gamma_first_sym with (gamma := pre ++ NT y :: suf); eauto.
      + eapply sized_ns_np; eauto.
        eapply nullable_middle_sym; eauto.
    - destruct Hl as [Hfg | [Hng' Hfo]].
      + exfalso; eapply no_first_follow_conflicts with (sym := NT x); eauto.
        eapply first_gamma_first_sym with (gamma := pre ++ NT y :: suf); eauto.
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
      -> exists gamma f,
        In (existT _ (x, gamma) f) g.(prods)
        /\ lookahead_for la x gamma g.
  Proof.
    intros g la x y Hn; inv Hn; eauto.
  Qed.

  Lemma LL1_parse_table_impl_no_left_recursion :
    forall (g : grammar) (tbl : parse_table) 
           (x : nonterminal) (la : lookahead),
      parse_table_correct tbl g
      -> ~ left_recursive g (NT x) la.
  Proof.
    intros g t x la Ht; unfold not; intros Hlr; red in Hlr.
    assert (Hex : exists gamma f,
               In (existT _ (x, gamma) f) g.(prods)
               /\ lookahead_for la x gamma g).
    { apply nullable_path_exists_production in Hlr; auto. }
    destruct Hex as [gamma [f [Hi Hl]]].
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

  Lemma nullable_path_ex_nt:
    forall g la sym sym',
      nullable_path g la sym sym'
      -> exists (x y : nonterminal),
        sym = NT x /\ sym' = NT y.
  Proof.
    intros; inv H; eauto.
  Qed.

  Lemma input_length_lt_or_nullable_sym :
    forall g tbl,
      parse_table_correct tbl g
      -> forall (ts  : list token)
                (vis : NtSet.t)
                (sa  : sym_arg),
        match sa with
        | F_arg s =>
          forall a v r Hle,
            parseSymbol tbl s ts vis a = inr (v, existT _ r Hle)
            -> List.length r < List.length ts
               \/ nullable_sym g s
        | G_arg gamma =>
          forall a vs r Hle,
            parseGamma tbl gamma ts vis a = inr (vs, existT _ r Hle)
            -> List.length r < List.length ts
               \/ nullable_gamma g gamma
        end.
  Proof.
    intros g tbl Htbl ts.
    induct_list_length ts.
    intros vis; induct_card tbl vis.
    intros sa; induct_sa_size sa.
    destruct sa.
    - intros a v r Hle Hp; destruct a; simpl in *; dms; tc.
      + invh; auto.
      + step_eq Hpf; dms; tc.
        invh.
        pose proof e as e'; apply Htbl in e'; destruct e' as [Heq [Hin Hlk]].
        eapply IHcard with (sa := G_arg l) in Hpf; destruct Hpf; eauto.
        eapply cardinal_diff_add_lt; eauto.
    - intros a vs r Hle Hpf; destruct a; simpl in *; dms; tc.
      + invh; auto.
      + step_eq Hp; dms; tc.
        * step_eq Hpf'; dms; tc; invh.
          left; dlle; omega.
        * step_eq Hpf'; dms; tc; invh.
          dlle; try (left; omega).
          eapply IHsz with (sa := F_arg s)
                           (m  := sa_size (F_arg s)) in Hp;
            try (simpl; omega).
          eapply IHsz with (sa := G_arg l) in Hpf'; eauto.
          destruct Hp; destruct Hpf'; try omega; eauto.
  Qed.

  Lemma input_length_eq_nullable_sym :
    forall (g   : grammar)
           (tbl : parse_table)
           (s   : symbol)
           (ts  : list token)
           (vis : NtSet.t)
           (a : Acc triple_lt (meas tbl ts vis (F_arg s)))
           (v   : symbol_semty s)
           Hle,
        parse_table_correct tbl g
        -> parseSymbol tbl s ts vis a = inr (v, existT _ ts Hle)
        -> nullable_sym g s.
  Proof.
    intros g tbl s ts vis a v Hle Htbl Hp.
    eapply input_length_lt_or_nullable_sym with (sa := F_arg s) in Hp; eauto.
    destruct Hp; try omega; auto.
  Qed.

    Lemma error_conditions :
    forall g tbl,
      parse_table_correct tbl g
      -> forall (ts : list token)
                (vis : NtSet.t)
                (sa : sym_arg),
        match sa with
        | F_arg s =>
          forall a m x ts',
            parseSymbol tbl s ts vis a = inl (Error m x ts')
            -> (NtSet.In x vis
                /\ (s = NT x
                    \/ nullable_path g (peek ts) s (NT x)))
               \/ exists la, left_recursive g (NT x) la
        | G_arg gamma =>
          forall a m x ts',
            parseGamma tbl gamma ts vis a = inl (Error m x ts')
            -> (exists pre s suf,
                   gamma = pre ++ s :: suf
                   /\ nullable_gamma g pre
                   /\ NtSet.In x vis
                   /\ (s = NT x
                       \/ nullable_path g (peek ts) s (NT x)))
               \/ exists la, (left_recursive g (NT x) la)
        end.
  Proof.
    intros g tbl Ht ts.
    induct_list_length ts.
    intros vis; induct_card tbl vis.
    intros sa; induct_sa_size sa.
    destruct sa.
    - (* sa = F_arg sym *)
      intros a m x ts' Hp; destruct a; simpl in *; dms; tc.
      + inv Hp; left; auto.
      + step_eq Hpf; dms; tc.
        inv Hp.
        (* tactic *)
        eapply IHcard with (sa := G_arg l) in Hpf; eauto.
        * destruct Hpf as [Hex | Hex]; auto.
          destruct Hex as [pre [sym [suf [Hg [Hng [Hin Hrest]]]]]]; subst.
          apply Ht in e; destruct e as [Heq [Hin' Hlk]].
          destruct (NtSetFacts.eq_dec x n); subst.
          -- right; exists (peek input).
             destruct Hrest as [Heq' | Hnp]; subst.
             ++ eapply DirectPath; eauto.
             ++ pose proof Hnp as Hnp'.
                apply nullable_path_ex_nt in Hnp.
                destruct Hnp as [x [x' [Heq' Heq'']]]; subst.
                eapply IndirectPath; eauto.
          -- left; split; try ND.fsetdec.
             destruct Hrest as [Heq' | Hnp]; subst; eauto.
             pose proof Hnp as Hnp'.
             apply nullable_path_ex_nt in Hnp.
             destruct Hnp as [y [y' [Heq' Heq'']]]; subst.
             right; eauto.
        * eapply cardinal_diff_add_lt; eauto.
      + exfalso.
        inv Hp; eapply Ht in e; destruct e as [Heq [Hin Hlk]]; tc.

    - intros a m x ts' Hpf; destruct a; simpl in *; dms; tc.
      step_eq Hp.
      + invh.
        eapply IHsz with (sa := F_arg s) (m := sa_size (F_arg s)) in Hp;
          try (simpl; omega); eauto.
        destruct Hp as [Hin | Hex]; auto.
        left; exists nil; exists s; exists l; split; auto.
      + dms; step_eq Hpf'; dms; tc; invh.
        * eapply IHl with (sa := G_arg l) in Hpf'; eauto.
          destruct Hpf' as [Hex | Hex]; eauto.
          destruct Hex as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]]; ND.fsetdec.
        * eapply IHsz with (sa := G_arg l) in Hpf'; eauto.
          destruct Hpf'; eauto.
          destruct H as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]]; subst.
          left; exists (s :: pre); exists sym; exists suf; repeat split; auto.
          eapply input_length_eq_nullable_sym in Hp; eauto.
  Qed.

End ParserSafetyFn.

