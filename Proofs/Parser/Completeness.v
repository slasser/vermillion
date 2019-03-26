Require Import List.
Require Import Omega.
Require Import String.
Require Import Grammar.
Require Import ParseTree.
Require Import Tactics.
Require Import Utils.
Require Import Derivation.
Require Import Parser.
Require Import ParseTable.
Require Import ParseTableGen.
Require Import Proofs.Lemmas.
Import ListNotations.

Inductive nullable_path g (la : lookahead) :
  symbol -> symbol -> Prop :=
| DirectPath : forall x z gamma pre suf,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT z :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path g la (NT x) (NT z)
| IndirectPath : forall x y z gamma pre suf,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT y :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path g la (NT y) (NT z)
    -> nullable_path g la (NT x) (NT z).

Definition left_recursive g sym la :=
  nullable_path g la sym sym.

Inductive fg' (g : grammar) (la : lookahead) :
  list symbol -> Prop :=
| fg_hd : forall h t,
    first_sym g la h
    -> fg' g la (h :: t)
| fg_tl : forall h t,
    nullable_sym g h
    -> fg' g la t
    -> fg' g la (h :: t).

Lemma fg_fg' :
  forall g la gamma,
    first_gamma g la gamma <-> fg' g la gamma.
Proof.
  intros g la gamma; split; intros H.
  - inv H.
    revert H0.
    revert H1.
    revert s gsuf.
    induction gpre; intros; simpl in *.
    + constructor; auto.
    + inv H0.
      apply fg_tl; auto.
  - induction H.
    + rewrite <- app_nil_l.
      constructor; auto.
    + inv IHfg'.
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
  apply fg_fg'.
  apply fg_tl; auto.
  apply fg_fg'.
  auto.
Qed.

Lemma follow_pre :
  forall g x la sym suf pre,
    In (x, pre ++ suf) (productions g)
    -> In sym pre
    -> nullable_gamma g pre
    -> first_gamma g la suf
    -> follow_sym g la sym.
Proof.
  intros.
  apply in_split in H0.
  destruct H0 as [l1 [l2 Heq]].
  subst.
  destruct sym.
  - exfalso.
    eapply Lemmas.gamma_with_terminal_not_nullable; eauto. 
  - replace ((l1 ++ NT n :: l2) ++ suf) with (l1 ++ NT n :: (l2 ++ suf)) in H.
    + eapply FollowRight; eauto.
      apply Lemmas.nullable_split in H1.
      inv H1.
      apply first_gamma_split; auto.
    + rewrite cons_app_singleton.
      rewrite app_assoc.
      rewrite app_assoc.
      replace (((l1 ++ [NT n]) ++ l2)) with (l1 ++ NT n :: l2).
      * auto.
      * rewrite <- app_assoc; simpl; auto.
Qed.

Inductive first_sym_i (g : grammar) : lookahead -> symbol -> nat -> Prop :=
  FirstT_i : forall y : terminal, first_sym_i g (LA y) (T y) 0
| FirstNT_i : forall (x : nonterminal) (gpre : list symbol)
                   (s : symbol) (gsuf : list symbol)
                (la : lookahead) (n : nat),
              In (x, gpre ++ s :: gsuf) (productions g) ->
              nullable_gamma g gpre ->
              first_sym_i g la s n -> first_sym_i g la (NT x) (S n).

Lemma first_sym_exists_size :
  forall g la sym,
    first_sym g la sym
    -> exists n, first_sym_i g la sym n.
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
    first_sym_i g la sym n
    -> first_sym g la sym.
Proof.
  intros g la sym n Hf; induction Hf; auto.
  econstructor; eauto.
Qed.

Lemma first_sym_rhs_eqs :
  forall g t,
    parse_table_for t g
    -> forall x pre pre' sym sym' suf suf' la,
      In (x, pre ++ sym :: suf) (productions g)
      -> In (x, pre' ++ sym' :: suf') (productions g)
      -> nullable_gamma g pre
      -> nullable_gamma g pre'
      -> first_sym g la sym
      -> first_sym g la sym'
      -> pre = pre' /\ sym = sym' /\ suf = suf'.
Proof.
  intros g t Ht x pre pre' sym sym' suf suf' la Hi Hi' Hn Hn' Hf Hf'.
  assert (Heq: pre ++ sym :: suf = pre' ++ sym' :: suf').
  { assert (Hl : lookahead_for la x (pre ++ sym :: suf) g).
    { left; eauto. }
    assert (Hl' : lookahead_for la x (pre' ++ sym' :: suf') g).
    { left; eauto. }
    apply Ht in Hl; apply Ht in Hl'; auto.
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

Lemma first_sym_i_det :
  forall g t la sym n,
    parse_table_for t g
    -> first_sym_i g la sym n
    -> forall n',
        first_sym_i g la sym n'
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

Lemma first_sym_i_np :
  forall g la x y,
    nullable_path g la x y
    -> first_sym g la y
    -> exists nx ny,
        first_sym_i g la x nx
        /\ first_sym_i g la y ny
        /\ ny < nx.
Proof.
  intros g la x y Hn.
  induction Hn; intros; subst.
  - apply first_sym_exists_size in H3.
    destruct H3.
    assert (first_sym_i g la (NT x) (S x0)).
    { econstructor; eauto. }
    exists (S x0); exists x0; split; auto.
  - apply IHHn in H3.
    destruct H3 as [nx [ny [Hf [Hf' Hlt]]]].
    assert (first_sym_i g la (NT x) (S nx)).
    { econstructor; eauto. }
    exists (S nx); exists ny; split; auto.
Qed.

Inductive sized_nullable_sym (g : grammar) : symbol -> nat -> Prop :=
    SzNullableSym : forall (x : nonterminal)
                           (ys : list symbol)
                           (n : nat),
    In (x, ys) (productions g) ->
    sized_nullable_gamma g ys n ->
    sized_nullable_sym g (NT x) (S n)
  with sized_nullable_gamma (g : grammar) : list symbol -> nat -> Prop :=
    SzNullableNil : sized_nullable_gamma g [] 0
  | SzNullableCons : forall (hd : symbol) (tl : list symbol)(n n' : nat),
                   sized_nullable_sym g hd n ->
                   sized_nullable_gamma g tl n' ->
                   sized_nullable_gamma g (hd :: tl) (n + n').

Scheme sized_nullable_sym_mutual_ind := Induction for sized_nullable_sym Sort Prop
  with sized_nullable_gamma_mutual_ind := Induction for sized_nullable_gamma Sort Prop.

Lemma sized_ns_ns :
  forall g sym n,
    sized_nullable_sym g sym n -> nullable_sym g sym.
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
    sized_nullable_gamma g gamma n -> nullable_gamma g gamma.
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
    parse_table_for t g
    -> sized_nullable_sym g sym n
    -> follow_sym g la sym
    -> forall n', sized_nullable_sym g sym n' -> n = n'.
Proof.
  intros g t la sym n Ht Hs.
  induction Hs using sized_nullable_sym_mutual_ind with
      (P := fun sym n (H : sized_nullable_sym g sym n) =>
              follow_sym g la sym
              -> forall n', sized_nullable_sym g sym n' -> n = n')
      (P0 := fun gsuf n (H : sized_nullable_gamma g gsuf n) =>
               forall x gpre n',
                 In (x, gpre ++ gsuf) (productions g)
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
      * constructor; auto.
      * omega.
    + apply IHgamma in H; auto.
      destruct H as [n [n' [Hs [Hs' Hle]]]].
      apply sized_ns_ex in H3.
      destruct H3.
      exists n.
      exists (x + n').
      repeat split; auto.
      * constructor; auto.
      * omega.
Qed.

Lemma sized_ns_np :
  forall g x y pre suf,
    In (x, pre ++ NT y :: suf) (productions g)
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
    parse_table_for t g
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
      -> exists gamma, In (x, gamma) (productions g)
                       /\ lookahead_for la x gamma g.
Proof.
  intros g la x y Hn; inv Hn; eauto.
Qed.

Lemma LL1_parse_table_impl_no_left_recursion :
  forall g t la x,
    parse_table_for t g
    -> ~ left_recursive g (NT x) la.
Proof.
  intros g t la x Ht; unfold not; intros Hlr; red in Hlr.
  assert (Hex : exists gamma,
             In (x, gamma) (productions g)
             /\ lookahead_for la x gamma g).
  { apply nullable_path_exists_production in Hlr; auto. }
  destruct Hex as [gamma [Hi Hl]].
  destruct Hl as [Hfg | [Hng Hfo]].
  - assert (Hf : first_sym g la (NT x)) by (inv Hfg; eauto).
    eapply first_sym_i_np in Hf; eauto.
    destruct Hf as [n [n' [Hf [Hf' Hlt]]]].
    eapply first_sym_i_det in Hf; eauto.
    omega.
  - assert (Hns : nullable_sym g (NT x)) by eauto.
    eapply exist_decreasing_nullable_sym_sizes_in_null_path in Hns; eauto.
    destruct Hns as [n [n' [Hs [Hs' Hlt]]]].
    eapply sized_nullable_sym_det in Hs; eauto.
    omega.
Qed.

Inductive nlr_tree_der (g : grammar) :
  symbol -> list string -> NtSet.t -> tree -> list string -> Prop :=
| T_nlr :
    forall (y : terminal) (vis : NtSet.t) (rem : list string),
      nlr_tree_der g (T y) [y] vis (Leaf y) rem
| NT_nlr :
    forall (x : nonterminal) 
           (gamma : list symbol)
           (word rem : list terminal)
           (vis : NtSet.t)
           (subtrees : list tree),
      In (x, gamma) g.(productions)
      -> lookahead_for (peek (word ++ rem)) x gamma g
      -> ~ NtSet.In x vis
      -> nlr_forest_der g gamma word (NtSet.add x vis) subtrees rem
      -> nlr_tree_der g (NT x) word vis (Node x subtrees) rem
with nlr_forest_der (g : grammar) :
       list symbol -> list string -> NtSet.t -> list tree -> list string -> Prop :=
     | Nil_nlr : forall vis rem,
         nlr_forest_der g [] [] vis [] rem
     | ConsNull_nlr : forall hdSym tlSyms wsuf rem vis hdTree tlTrees,
         nlr_tree_der g hdSym [] vis hdTree (wsuf ++ rem)
         -> nlr_forest_der g tlSyms wsuf vis tlTrees rem
         -> nlr_forest_der g (hdSym :: tlSyms)
                                    wsuf
                                    vis
                                    (hdTree :: tlTrees)
                                    rem
     | ConsNonNull_nlr : forall hdSym tlSyms wpre wsuf rem vis hdTree tlTrees,
         wpre <> []
         -> nlr_tree_der g hdSym wpre vis hdTree (wsuf ++ rem)
         -> nlr_forest_der g tlSyms wsuf NtSet.empty tlTrees rem
         -> nlr_forest_der g (hdSym :: tlSyms)
                             (wpre ++ wsuf)
                             vis
                             (hdTree :: tlTrees)
                             rem.

Scheme nlr_tree_mutual_ind := Induction for nlr_tree_der Sort Prop
  with nlr_forest_mutual_ind := Induction for nlr_forest_der Sort Prop.

Lemma lookups_neq_contra :
  forall x la t gamma,
    pt_lookup x la t = Some gamma
    -> pt_lookup x la t = None
    -> False.
Proof.
  intros; congruence.
Qed.

Lemma lookups_eq :
  forall x la t gamma gamma',
    pt_lookup x la t = Some gamma
    -> pt_lookup x la t = Some gamma'
    -> gamma = gamma'.
Proof.
  intros; tc.
Qed.

Lemma lookahead_for_ptlk_dec :
  forall g t x gamma la,
    parse_table_for t g
    -> In (x, gamma) (productions g)
    -> lookahead_for la x gamma g
    -> exists (pf : pt_lookup x la t = Some gamma),
        ptlk_dec x la t = inr (exist _ gamma pf).
Proof.
  intros.
  destruct (ptlk_dec x la t).
  - apply H in H1; auto; tc.
  - destruct s.
    apply H in H1; auto.
    assert (gamma = x0) by congruence; subst.
    exists e; auto.
Qed.


Lemma non_nil_list_length :
  forall A (xs : list A),
    xs <> [] -> List.length xs > 0.
Proof.
  intros; destruct xs; simpl in *; tc.
  omega.
Qed.

Lemma app_length_lt :
  forall A (xs ys : list A), xs <> [] -> List.length ys < List.length (xs ++ ys).
Proof.
  intros.
  apply non_nil_list_length in H.
  destruct xs; simpl in *.
  - omega.
  - rewrite app_length; omega.
Qed.

Lemma parse_complete_wrt_nlr :
  forall g tbl sym word rem vis a tr,
    parse_table_for tbl g
    -> nlr_tree_der g sym word vis tr rem
    ->
        exists Hle,
          parse_nf tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle).
Proof.
  intros g tbl sym word rem vis a tr Ht Hd.
  induction Hd using nlr_tree_mutual_ind with
      (P := fun sym word vis tr rem (H : nlr_tree_der g sym word vis tr rem) =>
              forall a,
                exists Hle,
                parse_nf tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle))

      (P0 := fun gamma word vis f rem (H : nlr_forest_der g gamma word vis f rem) =>
               forall a,
                 exists Hle,
                   parseForest_nf tbl gamma (word ++ rem) vis a = inr (f, existT _ rem Hle)).

  - destruct a; simpl.
    step; tc.
    exists (length_lt_eq_cons _ (y :: rem) y rem eq_refl).
    eauto.

  - assert (Hacc : Acc triple_lt
                 (meas tbl (word ++ rem) 
                       (NtSet.add x vis) (G_arg gamma))).
    { apply triple_lt_wf. }
    destruct a.
    step.
    + apply Ht in l; auto.
      exfalso; eapply lookups_neq_contra; eauto.
    + destruct s as [gamma' Hlk].
      step; tc.
      assert (gamma = gamma').
      { apply Ht in l; auto.
        eapply lookups_eq; eauto. }
      subst.
      step_eq Hpf.
      * edestruct IHHd as [Hle Hpf']; clear IHHd.
        erewrite Hpf in Hpf'.
        congruence.
      * edestruct IHHd as [Hle Hpf']; clear IHHd.
        erewrite Hpf in Hpf'.
        inv Hpf'.
        eauto.

  - destruct a; simpl; eauto.

  - destruct a.
    simpl.
    edestruct IHHd as [Hle Hp].
    rewrite Hp.
    clear IHHd; clear Hp.
    destruct Hle.
    + simpl in l.
      omega.
    + edestruct IHHd0 as [Hle Hpf].
      rewrite Hpf.
      eexists; eauto.

  - destruct a; simpl.
    rewrite app_assoc in IHHd.
    edestruct IHHd as [Hle Hp].
    rewrite Hp; clear IHHd; clear Hp.
    step.
    + edestruct IHHd0 as [Hle Hpf].
      rewrite Hpf; clear IHHd0; clear Hpf.
      eauto.
    + exfalso.
      rewrite <- app_assoc in e.
      symmetry in e.
      apply l_ident_eq_nil in e.
      congruence.
Qed.

(*Lemma parse_complete_wrt_nlr :
  forall g tbl sym word rem vis a tr,
    parse_table_for tbl g
    -> nlr_tree_der g sym word vis tr rem
    -> exists Hle,
        parse_nf tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle).
Proof.
  intros g tbl sym word rem vis a tr Ht Hd.
  induction Hd using nlr_tree_mutual_ind with
      (P := fun sym word vis tr rem (H : nlr_tree_der g sym word vis tr rem) =>
              forall a,
                exists Hle,
                parse_nf tbl sym (word ++ rem) vis a = inr (tr, existT _ rem _))

      (P0 := fun gamma word vis f rem (H : nlr_forest_der g gamma word vis f rem) =>
               forall a,
                 exists Hle,
                   parseForest_nf tbl gamma (word ++ rem) vis a = inr (f, existT _ rem _)).

  - destruct a; simpl.
    step; tc.
    exists (length_le_dec_cons _ (y :: rem) y rem eq_refl).
    eauto.

  - destruct a; simpl.
    step.
    + apply Ht in l; auto.
      (* not sure why we need a lemma instead of using congruence here *)
      exfalso; eapply lookups_neq_contra; eauto.
    + destruct s as [gamma' Hlk].
      step; tc.
      assert (gamma = gamma').
      { apply Ht in l; auto.
        eapply lookups_eq; eauto. }
      subst.
      rewrite IHHd; auto.

  - destruct a; simpl; auto.

  - destruct a; simpl.
    rewrite IHHd.
    step; try omega.
    rewrite IHHd0; auto.

  - destruct a; simpl.
    rewrite app_assoc in IHHd.
    rewrite IHHd.
    step.
    + rewrite IHHd0; auto.
    + exfalso.
      apply n1.
      simpl in *.
      rewrite <- app_assoc.
      apply app_length_lt; auto.
Qed.
 *)

Fixpoint nullTree (tr : tree) : bool :=
  match tr with
  | Leaf _ => false
  | Node _ sts =>
    let fix nullForest (l : list tree) : bool :=
        match l with
        | [] => true
        | t :: l' => andb (nullTree t) (nullForest l')
        end
    in  nullForest sts
  end.

Fixpoint nullForest (l : list tree) : bool :=
  match l with
  | [] => true
  | t :: l' => andb (nullTree t) (nullForest l')
  end.
    
Lemma nullTree_nullable_sym :
  forall g sym word tr rem,
    (@sym_derives_prefix g) sym word tr rem
    -> nullTree tr = true
    -> nullable_sym g sym.
Proof.
  intros g sym word tr rem Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              nullTree tr = true
              -> nullable_sym g sym)

      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               nullForest f = true
               -> nullable_gamma g gamma).
                 
  - intros Hn; inv Hn.
    
  - intros Hn; simpl in *.
    fold nullForest in Hn.
    apply IHHd in Hn.
    econstructor; eauto.

  - intros; constructor.

  - intros Hn; simpl in *.
    apply andb_prop in Hn.
    destruct Hn as [Hhd Htl].
    apply IHHd in Hhd.
    apply IHHd0 in Htl.
    econstructor; eauto.
Qed.

Lemma nullTree_word_eq_nil :
  forall g sym word tr rem,
    (@sym_derives_prefix g) sym word tr rem
    -> nullTree tr = true
    -> word = [].
Proof.
  intros g sym word tr rem Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              nullTree tr = true
              -> word = [])

      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               nullForest f = true
               -> word = []).

  - intros Hn; inv Hn.

  - intros Hn; simpl in *.
    apply IHHd in Hn; auto.

  - intros; auto.

  - intros Hn; simpl in *.
    apply andb_prop in Hn; destruct Hn as [Hhd Htl].
    apply IHHd in Hhd.
    apply IHHd0 in Htl.
    subst; auto.
Qed.

Lemma nullTree_word_neq_nil :
  forall g sym word tr rem,
    (@sym_derives_prefix g) sym word tr rem
    -> nullTree tr = false
    -> word <> [].
Proof.
  intros g sym word tr rem Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              nullTree tr = false
              -> word <> [])

      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               nullForest f = false
               -> word <> []).

  - intros Hn; unfold not; intros He.
    inv He.

  - intros Hn; unfold not; intros He; subst; simpl in *.
    apply IHHd in Hn; tc.

  - intros Hn; inv Hn.

  - intros Hn; unfold not; intros He; simpl in *.
    apply app_eq_nil in He.
    destruct He as [Hpre Hsuf]; subst.
    apply Bool.andb_false_iff in Hn.
    destruct Hn as [Hhd | Htl].
    + apply IHHd in Hhd; tc.
    + apply IHHd0 in Htl; tc.
Qed.
    
Fixpoint reachableNts (tr : tree) : NtSet.t :=
  match tr with
  | Leaf _ => NtSet.empty
  | Node x sts =>
    let fix reachableNtsF (l : list tree) : NtSet.t :=
        match l with
        | [] => NtSet.empty
        | t :: l' => if nullTree t then
                       NtSet.union (reachableNts t) (reachableNtsF l')
                     else
                       reachableNts t
        end
    in  NtSet.add x (reachableNtsF sts)
  end.

Fixpoint reachableNtsF (l : list tree) : NtSet.t :=
  match l with
  | [] => NtSet.empty
  | t :: l' => if nullTree t then
                 NtSet.union (reachableNts t) (reachableNtsF l')
               else
                 reachableNts t
  end.

Lemma nullable_path_isNT :
  forall g la sym sym',
    nullable_path g la sym sym'
    -> isNT sym = true /\ isNT sym' = true.
Proof.
  intros g la sym sym' Hnp; inv Hnp; auto.
Qed.
  
Lemma reachableNts_nullable_path :
  forall g sym word tr rem,
    (@sym_derives_prefix g) sym word tr rem
    -> forall x,
      NtSet.In x (reachableNts tr)
      -> sym = NT x
         \/ nullable_path g (peek (word ++ rem)) sym (NT x).
Proof.
  intros g sym word tr rem Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              forall x : NtSet.elt,
                NtSet.In x (reachableNts tr) ->
                sym = NT x \/
                nullable_path g (peek (word ++ rem)) sym (NT x))
      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               forall x,
                 NtSet.In x (reachableNtsF f)
                 -> exists pre sym suf,
                   gamma = pre ++ sym :: suf
                   /\ nullable_gamma g pre
                   /\ (sym = NT x
                       \/ nullable_path g (peek (word ++ rem)) sym (NT x))).

  - intros x Hi; simpl in *.
    inv Hi.

  - intros x' Hi; simpl in *.
    destruct (NtSetFacts.eq_dec x x'); subst; auto.
    fold reachableNtsF in Hi.
    apply NtSetFacts.add_3 in Hi; auto.
    apply IHHd in Hi; clear IHHd.
    destruct Hi as [pre [sym [suf [He [Hng [He' | Hnp]]]]]]; subst.
    + right.
      eapply DirectPath; eauto.
    + destruct sym as [y | x''].
      * apply nullable_path_isNT in Hnp.
        destruct Hnp as [Hcontra _]; inv Hcontra.
      * right; eapply IndirectPath; eauto.

  - intros x Hi; simpl in *.
    inv Hi.

  - intros x Hi; simpl in *.
    destruct (nullTree hdTree) eqn:Hn.
    + pose proof Hn as Hn'.
      eapply nullTree_nullable_sym in Hn; eauto.
      eapply nullTree_word_eq_nil in Hn'; eauto; subst; simpl in *.
      apply NtSetFacts.union_1 in Hi.
      destruct Hi as [Hhd | Htl].
      * apply IHHd in Hhd.
        exists []; exists hdRoot; exists tlRoots; simpl.
        repeat split; auto.
      * apply IHHd0 in Htl.
        destruct Htl as [pre [sym [suf [Heq [Hng [Heq' | Hnp]]]]]]; subst.
        -- exists (hdRoot :: pre); exists (NT x); exists suf; simpl.
           repeat split; auto.
        -- exists (hdRoot :: pre); exists sym; exists suf; simpl.
           repeat split; auto.
    + apply IHHd in Hi.
      exists []; exists hdRoot; exists tlRoots; simpl.
      repeat split; auto.
      rewrite <- app_assoc; auto.
Qed.

Lemma reachableNtsF_nullable_path :
  forall g gamma word f rem,
    (@gamma_derives_prefix g) gamma word f rem
    -> forall x,
      NtSet.In x (reachableNtsF f)
      -> exists pre sym suf,
        gamma = pre ++ sym :: suf
        /\ nullable_gamma g pre
        /\ (sym = NT x
            \/ nullable_path g (peek (word ++ rem)) sym (NT x)).
Proof.
  intros g gamma word f rem Hd.
  induction Hd using gdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              forall x : NtSet.elt,
                NtSet.In x (reachableNts tr) ->
                sym = NT x \/
                nullable_path g (peek (word ++ rem)) sym (NT x))
      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               forall x,
                 NtSet.In x (reachableNtsF f)
                 -> exists pre sym suf,
                   gamma = pre ++ sym :: suf
                   /\ nullable_gamma g pre
                   /\ (sym = NT x
                       \/ nullable_path g (peek (word ++ rem)) sym (NT x))).

  - intros x Hi; simpl in *.
    inv Hi.

  - intros x' Hi; simpl in *.
    destruct (NtSetFacts.eq_dec x x'); subst; auto.
    fold reachableNtsF in Hi.
    apply NtSetFacts.add_3 in Hi; auto.
    apply IHHd in Hi; clear IHHd.
    destruct Hi as [pre [sym [suf [He [Hng [He' | Hnp]]]]]]; subst.
    + right.
      eapply DirectPath; eauto.
    + destruct sym as [y | x''].
      * apply nullable_path_isNT in Hnp.
        destruct Hnp as [Hcontra _]; inv Hcontra.
      * right; eapply IndirectPath; eauto.

  - intros x Hi; simpl in *.
    inv Hi.

  - intros x Hi; simpl in *.
    destruct (nullTree hdTree) eqn:Hn.
    + pose proof Hn as Hn'.
      eapply nullTree_nullable_sym in Hn; eauto.
      eapply nullTree_word_eq_nil in Hn'; eauto; subst; simpl in *.
      apply NtSetFacts.union_1 in Hi.
      destruct Hi as [Hhd | Htl].
      * apply IHHd in Hhd.
        exists []; exists hdRoot; exists tlRoots; simpl.
        repeat split; auto.
      * apply IHHd0 in Htl.
        destruct Htl as [pre [sym [suf [Heq [Hng [Heq' | Hnp]]]]]]; subst.
        -- exists (hdRoot :: pre); exists (NT x); exists suf; simpl.
           repeat split; auto.
        -- exists (hdRoot :: pre); exists sym; exists suf; simpl.
           repeat split; auto.
    + apply IHHd in Hi.
      exists []; exists hdRoot; exists tlRoots; simpl.
      repeat split; auto.
      rewrite <- app_assoc; auto.
Qed.    

Lemma nullable_path_from_root_to_subtree_reachableNts :
  forall g sym word x x' sts rem,
    (@sym_derives_prefix g) sym word (Node x sts) rem
    -> NtSet.In x' (reachableNtsF sts)
    -> nullable_path g (peek (word ++ rem)) sym (NT x').
Proof.
  intros g sym word x x' sts rem Hd Hi.
  inversion Hd as [g' y rem' | x'' gamma word' rem' sts' Hi' Hl Hg]; subst; clear Hd.
  eapply reachableNtsF_nullable_path in Hg; eauto.
  destruct Hg as [pre [sym [suf [He [Hng [He' | Hnp]]]]]]; subst.
  + eapply DirectPath; eauto.
  + destruct sym as [y | x''].
    * eapply nullable_path_isNT in Hnp.
      destruct Hnp as [Hcontra _]; inv Hcontra.
    * eapply IndirectPath; eauto.
Qed.

Lemma LL1_tree_root_not_in_subtree_reachableNts :
  forall g t sym word x sts rem,
    parse_table_for t g
    -> (@sym_derives_prefix g) sym word (Node x sts) rem
    -> ~ NtSet.In x (reachableNtsF sts).
Proof.
  intros g t sym word x sts rem Ht Hd; unfold not; intros Hi.
  pose proof Hd as Hd'.
  inv Hd.
  eapply LL1_parse_table_impl_no_left_recursion; eauto.
  red.
  eapply nullable_path_from_root_to_subtree_reachableNts; eauto.
Qed.

Lemma empty_inter_add :
  forall (x : nonterminal) (a b : NtSet.t),
    NtSet.Empty (NtSet.inter a (NtSet.add x b))
    -> ~ NtSet.In x b
    -> NtSet.Empty (NtSet.inter (NtSet.add x a) b).
Proof.
  intros.
  ND.fsetdec.
Qed.

Lemma derives_derives' :
  forall g t sym input tr rem,
    parse_table_for t g
    -> (@sym_derives_prefix g) sym input tr rem
    -> forall vis,
      NtSet.Empty (NtSet.inter vis (reachableNts tr))
      -> nlr_tree_der g sym input vis tr rem.
Proof.
  intros g t sym input tr rem Ht Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) => forall vis,
                NtSet.Empty (NtSet.inter vis (reachableNts tr))
                -> nlr_tree_der g sym word vis tr rem)

      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               forall vis,
                 NtSet.Empty (NtSet.inter vis (reachableNtsF f))
                 -> nlr_forest_der g gamma word vis f rem).

  - intros vis He; simpl in *.
    constructor.

  - intros vis He; simpl in *.
    fold reachableNtsF in He.
    econstructor; eauto.
    + ND.fsetdec.
    + apply IHHd; clear IHHd.
      apply empty_inter_add; auto.
      eapply LL1_tree_root_not_in_subtree_reachableNts; eauto.
      econstructor; eauto.

  - intros vis He; simpl in *.
    constructor.

  - intros vis He; simpl in *.
    destruct (nullTree hdTree) eqn:Hn.
    + pose proof Hn as Hn'.
      eapply nullTree_word_eq_nil in Hn; eauto; subst; simpl in *.
      apply ConsNull_nlr.
      * apply IHHd.
        ND.fsetdec.
      * apply IHHd0.
        ND.fsetdec.
    + eapply nullTree_word_neq_nil in Hn; eauto.
      apply ConsNonNull_nlr; auto.
Qed.

Definition parse_wrapper tbl sym input :=
  parse_nf tbl sym input NtSet.empty (triple_lt_wf (meas tbl input NtSet.empty (F_arg sym))).

Theorem parse_nf_complete :
  forall g tbl sym word tr rem,
    parse_table_for tbl g
    -> (@sym_derives_prefix g) sym word tr rem
    -> exists Hle,
        parse_wrapper tbl sym (word ++ rem) = inr (tr, existT _ rem Hle).
Proof.
  intros.
  unfold parse_wrapper.
  eapply parse_complete_wrt_nlr; eauto.
  eapply derives_derives'; eauto.
Qed.
