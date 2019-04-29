Require Import MSets.
Require Import Wf_nat.

Require Import Generator.
Require Import Grammar.
Require Import Lemmas.
Require Import Vermillion.Tactics.

Import ListNotations.

Module NullableProofsFn (Import G : Grammar.T).

  Module Export Gen := GeneratorFn G.
  Module Import L   := LemmasFn G.

  Lemma mkNullableSet'_eq_body :
    forall (ps : list production)
           (nu : NtSet.t),
      mkNullableSet' ps nu =
      let nu' := nullablePass ps nu in
      if NtSet.eq_dec nu nu' then
        nu
      else
        mkNullableSet' ps nu'.
  Proof.
    intros ps nu.
    unfold mkNullableSet'.
    unfold mkNullableSet'_func.
    rewrite Wf.fix_sub_eq; auto.
    intros.
    match goal with
    | |- context[NtSet.eq_dec ?a ?b] => destruct (NtSet.eq_dec a b)
    end; auto.
  Qed.
  
  Lemma nu_sound_nullableGamma_sound :
    forall (g     : grammar)
           (nu    : NtSet.t)
           (gamma : list symbol),
      nullable_set_sound nu g
      -> nullableGamma gamma nu = true
      -> nullable_gamma g gamma.
  Proof.
    intros g nu gamma Hsou Hng.
    induction gamma as [| sym syms]; auto.
    destruct sym as [y | x].
    - inv Hng.
    - simpl in *.
      destruct (NtSet.mem x nu) eqn:Hmem.
      + rewrite NtSet.mem_spec in Hmem.
        apply Hsou in Hmem.
        econstructor; eauto.
      + inv Hng.
  Qed.
  
  Lemma cons_app_singleton :
    forall A (x : A) (ys : list A),
      x :: ys = [x] ++ ys.
  Proof.
    auto.
  Qed.
  
  Lemma in_app_cons :
    forall A (x : A) (pre suf : list A),
      In x (pre ++ x :: suf).
  Proof.
    intros A x pre suf.
    induction pre; simpl; auto.
  Qed.
  
  Lemma nullablePass_preserves_soundness' :
    forall (g  : grammar)
           (nu : NtSet.t),
      nullable_set_sound nu g
      -> forall suf pre : list production,
        pre ++ suf = (prodsOf g)
        -> nullable_set_sound (nullablePass suf nu) g.
  Proof. 
    intros g nu Hsou suf.
    induction suf as [| (x, gamma) suf]; intros pre Happ; simpl; auto.
    pose proof Happ as Happ'.
    rewrite cons_app_singleton in Happ.
    rewrite app_assoc in Happ.
    apply IHsuf in Happ.
    destruct (nullableGamma gamma (nullablePass suf nu)) eqn:Hng; auto.
    unfold nullable_set_sound.
    intros x' Hin.
    destruct (NtSetFacts.eq_dec x x'); subst.
    - assert (Hin' : In (x', gamma) (prodsOf g)).
      { rewrite <- Happ'; apply in_app_cons. }
      apply in_prodsOf_exists_in_xprods in Hin'.
      destruct Hin' as [f Hin']. 
      econstructor; eauto.
      eapply nu_sound_nullableGamma_sound; eauto.
    - apply NtSetFacts.add_3 in Hin; auto.
  Qed.
  
  Lemma nullablePass_preserves_soundness :
    forall (g  : grammar)
           (nu : NtSet.t),
      nullable_set_sound nu g
      -> nullable_set_sound (nullablePass (prodsOf g) nu) g.
  Proof.
    intros g nu Hsou.
    apply nullablePass_preserves_soundness' with (pre := []); auto.
  Qed.
  
  Lemma mkNullableSet'_preserves_soundness :
    forall (g  : grammar)
           (nu : NtSet.t),
      nullable_set_sound nu g
      -> nullable_set_sound (mkNullableSet' (prodsOf g) nu) g.
  Proof.
    intros g nu.
    remember (countNullableCandidates (prodsOf g) nu) as card.
    generalize dependent nu.
    induction card using lt_wf_ind.
    intros nu Hcard Hsou; subst.
    rewrite mkNullableSet'_eq_body; simpl.
    destruct (NtSet.eq_dec nu (nullablePass (prodsOf g) nu)) as [Heq | Hneq]; auto.
    eapply H; clear H; eauto.
    - apply nullablePass_neq_candidates_lt; auto. 
    - apply nullablePass_preserves_soundness; auto.
  Qed.
  
  Lemma empty_nu_sound :
    forall (g : grammar),
      nullable_set_sound NtSet.empty g.
  Proof.
    unfold nullable_set_sound; ND.fsetdec.
  Qed.
  
  Theorem mkNullableSet_sound :
    forall (g : grammar),
      nullable_set_sound (mkNullableSet g) g.
  Proof.
    intros g.
    unfold mkNullableSet.
    apply mkNullableSet'_preserves_soundness.
    apply empty_nu_sound.
  Qed.
  
  (* Completeness *)
  
  Lemma nullablePass_add_equal :
    forall ps x nu,
      NtSet.In x nu
      -> NtSet.Equal (nullablePass ps nu) (NtSet.add x (nullablePass ps nu)).
  Proof.
    intros ps.
    induction ps as [| (x', ys) ps]; intros x nu Hin; simpl in *.
    - ND.fsetdec.
    - destruct (nullableGamma ys (nullablePass ps nu)); auto.
      apply IHps in Hin; ND.fsetdec.
  Qed.
  
  Lemma nullable_gamma_nullableGamma_true :
    forall g ys nu,
      nullable_gamma g ys
      -> (forall x, In (NT x) ys -> NtSet.In x nu)
      -> nullableGamma ys nu = true.
  Proof.
    intros g.
    induction ys as [| sym syms]; intros nu Hng Hall; auto.
    destruct sym as [y | x].
    - inv Hng.
      inv H1. (* LEMMA *)
    - simpl. 
      assert (In (NT x) (NT x :: syms)) by (left; auto).
      apply Hall in H.
      rewrite <- NtSet.mem_spec in H.
      rewrite H.
      apply IHsyms.
      + inv Hng; auto.
      + firstorder.
  Qed.
  
  Lemma nu_equal_nullableGamma_eq :
    forall nu nu' gamma,
      NtSet.Equal nu nu'
      -> nullableGamma gamma nu = nullableGamma gamma nu'.
  Proof.
    intros nu nu' gamma.
    induction gamma as [| sym syms]; intros Heq; simpl in *; auto.
    destruct sym as [y | x]; auto.
    destruct (NtSet.mem x nu) eqn:Hmem; destruct (NtSet.mem x nu') eqn:Hmem'; auto.
    - rewrite NtSet.mem_spec in Hmem.
      apply Heq in Hmem.
      rewrite <- NtSet.mem_spec in Hmem; congruence.
    - rewrite NtSet.mem_spec in Hmem'.
      apply Heq in Hmem'.
      rewrite <- NtSet.mem_spec in Hmem'; congruence.
  Qed.
  
  Lemma nullablePass_right_in_left_in :
    forall (g  : grammar)
           (x  : nonterminal)
           (ys : list symbol)
           (suf pre : list production),
      pre ++ suf = (prodsOf g)
      -> In (x, ys) suf
      -> nullable_gamma g ys
      -> forall nu,
          NtSet.Equal nu (nullablePass suf nu)
          -> (forall x, In (NT x) ys -> NtSet.In x nu)
          -> NtSet.In x nu.
  Proof.
    intros g x ys suf.
    induction suf as [| (x', ys') suf]; intros pre Happ Hin Hng nu Heq Hall.
    - inv Hin.
    - destruct Hin.
      + inv H; simpl in *.
        destruct (nullableGamma ys (nullablePass suf nu)) eqn:Hf.
        * ND.fsetdec.
        * exfalso.
          eapply nullable_gamma_nullableGamma_true in Hng; eauto.
          erewrite nu_equal_nullableGamma_eq in Hng; eauto.
          congruence.
      + apply IHsuf with (pre := pre ++ [(x', ys')]); auto.
        * rewrite <- app_assoc; auto. 
        * simpl in *. 
          destruct (nullableGamma ys' (nullablePass suf nu)).
          -- assert (NtSet.In x' nu) by ND.fsetdec. 
             apply nullablePass_add_equal with (ps := suf) in H0.
             ND.fsetdec.
          -- auto.
  Qed.

(* Slight rephrasing of nullable_set_complete so that it's 
   compatible with induction on a nullable_sym judgment *)
Definition nullable_set_complete' nu g :=
  forall (sym : symbol)
         (x   : nonterminal), 
    nullable_sym g sym
    -> sym = NT x
    -> NtSet.In x nu.

(* Proof that it's equivalent *)
Lemma ns_complete'_complete :
  forall g nu,
    nullable_set_complete' nu g
    <-> nullable_set_complete nu g.
Proof.
  split; intros.
  - unfold nullable_set_complete; eauto.
  - unfold nullable_set_complete'; intros; subst; auto.
Qed.

(* Proof that when the iteration in mkNullableSet' converges, 
   the resulting  NULLABLE set is complete *)
Lemma nullablePass_equal_complete' :
  forall g nu,
    NtSet.Equal nu (nullablePass (prodsOf g) nu)
    -> nullable_set_complete' nu g.
Proof.
  intros g nu Heq.
  unfold nullable_set_complete'.
  intros sym x Hns.
  revert x.
  induction Hns using nullable_sym_mutual_ind with
      (P  := fun sym (pf : nullable_sym g sym) =>
               forall x, sym = NT x -> NtSet.In x nu)
      (P0 := fun gamma (pf : nullable_gamma g gamma) =>
               forall x, In (NT x) gamma -> NtSet.In x nu).
  - intros x' Heq'.
    inv Heq'.
    eapply nullablePass_right_in_left_in with 
        (pre := nil); simpl; eauto.
    eapply in_xprods_in_prodsOf; eauto.
  - intros x Hin.
    inv Hin.
  - intros x Hin.
    destruct Hin.
    + subst.
      apply IHHns; auto.
    + auto.
Qed.

Lemma nullablePass_equal_complete :
  forall g nu,
    NtSet.Equal nu (nullablePass (prodsOf g) nu)
    -> nullable_set_complete nu g.
Proof.
  intros.
  apply ns_complete'_complete.
  apply nullablePass_equal_complete'; auto.
Qed.

Lemma mkNullableSet'_complete :
  forall g nu,
    nullable_set_complete (mkNullableSet' (prodsOf g) nu) g.
Proof.
  intros g nu.
  remember (countNullableCandidates (prodsOf g) nu) as card.
  generalize dependent nu.
  induction card using lt_wf_ind.
  intros nu Hcard; subst.
  rewrite mkNullableSet'_eq_body; simpl.
  destruct (NtSet.eq_dec nu (nullablePass (prodsOf g) nu)) as [Heq | Hneq].
  - apply nullablePass_equal_complete; auto.
  - eapply H; clear H; eauto.
    apply nullablePass_neq_candidates_lt; auto.
Qed.

Theorem mkNullableSet_complete :
  forall g,
    nullable_set_complete (mkNullableSet g) g.
Proof.
  intros g.
  unfold mkNullableSet.
  apply mkNullableSet'_complete.
Qed.

(* Putting both mkNullableSet correctness properties into a single theorem *)

Theorem mkNullableSet_correct :
  forall (g : grammar),
    nullable_set_for (mkNullableSet g) g.
Proof.
  intros g.
  unfold nullable_set_for; split.
  - apply mkNullableSet_sound.
  - apply mkNullableSet_complete.
Qed.

End NullableProofsFn.

