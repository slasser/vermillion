Require Import MSets.
Require Import Wf_nat.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Import ListNotations.

Module MP := MSetProperties.Properties NtSet.

Lemma mkNullableSet'_eq_body :
  forall ps nu,
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

Lemma nullableGamma_sound_nu :
  forall g nu gamma,
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

(* Here's how I originally tried to write this lemma
   and ran into difficulty *)
Lemma nullablePass_preserves_soundness :
  forall g nu,
    nullable_set_sound nu g
    -> nullable_set_sound (nullablePass (productions g) nu) g.
Proof.
  intros g nu Hsou.
  induction (productions g) as [| (x, gamma) ps]; simpl; auto.
  destruct (nullableGamma gamma (nullablePass ps nu)) eqn:Hng; auto.
  unfold nullable_set_sound.
  intros x' Hin.
  destruct (NtSetFacts.eq_dec x x'); subst.
  - econstructor.
    + admit. (* I've lost the fact that (x', gamma) is a production in g *)
    + eapply nullableGamma_sound_nu; eauto.
  - apply NtSetFacts.add_3 in Hin; auto.
Abort.

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
      pre ++ suf = (productions g)
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
  - econstructor.
    + rewrite <- Happ'.
      apply in_app_cons.
    + eapply nullableGamma_sound_nu; eauto.
  - apply NtSetFacts.add_3 in Hin; auto.
Qed.

(* Another way to prove that nullablePass preserves soundness
   that I think is slightly less elegant *)
(*
Lemma nullablePass_preserves_soundness' :
  forall (g  : grammar)
         (nu : NtSet.t)
         (ps : list production),
    (forall x gamma,
        In (x, gamma) ps
        -> In (x, gamma) (productions g))
    -> nullable_set_sound nu g
    -> nullable_set_sound (nullablePass ps nu) g.
Proof. 
  intros g nu ps.
  induction ps as [| (x', gamma') ps]; intros Hsub Hsou; simpl; auto.
  assert (Hsub' : forall x gamma,
             In (x, gamma) ps -> In (x, gamma) (productions g)).
  { intros x gamma Hin.
    apply Hsub; right; auto. }
  apply IHps in Hsub'; auto.
  destruct (nullableGamma gamma' (nullablePass ps nu)) eqn:Hng; auto.
  unfold nullable_set_sound.
  intros x Hin.
  destruct (NtSetFacts.eq_dec x x'); subst.
  - econstructor.
    + apply Hsub; left; auto.
    + eapply nullableGamma_sound_nu; eauto.
  - apply NtSetFacts.add_3 in Hin; auto.
Qed.
*)

Lemma nullablePass_preserves_soundness :
  forall g nu,
    nullable_set_sound nu g
    -> nullable_set_sound (nullablePass (productions g) nu) g.
Proof.
  intros g nu Hsou.
  apply nullablePass_preserves_soundness' with
      (pre := []); auto.
Qed.

Lemma mkNullableSet'_preserves_soundness :
  forall (g : grammar)
         (nu : NtSet.t),
    nullable_set_sound nu g
    -> nullable_set_sound (mkNullableSet' (productions g) nu) g.
Proof.
  intros g nu.
  remember (numRemainingCandidates (productions g) nu) as card.
  generalize dependent nu.
  induction card using lt_wf_ind.
  intros nu Hcard Hsou; subst.
  rewrite mkNullableSet'_eq_body; simpl.
  destruct (NtSet.eq_dec nu (nullablePass (productions g) nu)) as [Heq | Hneq]; auto.
  eapply H; clear H; eauto.
  - destruct (nullablePass_eq_or_candidates_lt (productions g) nu); auto.
    unfold NtSet.eq in Hneq; congruence.
  - apply nullablePass_preserves_soundness; auto.
Qed.

Theorem mkNullableSet_sound :
  forall (g : grammar),
    nullable_set_sound (mkNullableSet g) g.
Proof.
  intros g.
  unfold mkNullableSet.
  apply mkNullableSet'_preserves_soundness.
  unfold nullable_set_sound; intros. (* LEMMA *)
  exfalso.
  rewrite <- NtSetFacts.empty_iff; eauto.
Qed.

(* Completeness *)

(* NtSet.eq nu (nullablePass (productions g) nu) *)

Definition nullable_set_complete' nu g :=
  forall (sym : symbol)
         (x : nonterminal), 
    nullable_sym g sym
    -> sym = NT x
    -> NtSet.In x nu.

Import MSetDecide.

Module Import NtSetDecide := WDecideOn NT_as_DT NtSet.

Lemma np_ng_in :
  forall nu pre x ys suf,
    NtSet.Equal nu (nullablePass (pre ++ (x, ys) :: suf) nu)
    -> nullableGamma ys (nullablePass (pre ++ (x, ys) :: suf) nu)  = true
    -> NtSet.In x nu.
Proof.
  intros nu pre.
  induction pre as [| (x', ys') pre]; intros x ys suf Heq Hng.
  - simpl in *.
    destruct (nullableGamma ys (nullablePass suf nu)) eqn:Hng'.
    + fsetdec.
    + congruence.
  - simpl in *.
    destruct (nullableGamma ys' (nullablePass (pre ++ (x, ys) :: suf) nu)) eqn:Hng'.
    + destruct (NtSetFacts.eq_dec x x').
      * subst; fsetdec.
Admitted.

Lemma nullablePass_equal_tl :
  forall ps nu,
    NtSet.Equal nu (nullablePass ps nu)
    -> forall suf pre,
      pre ++ suf = ps
      -> NtSet.Equal nu (nullablePass suf nu).
Proof.
  intros ps nu Heq suf.
  induction suf as [| (x, gamma) suf]; intros pre Happ.
  - simpl in *.
    apply MP.equal_refl.
  - simpl in *.
    destruct (nullableGamma gamma (nullablePass suf nu)) eqn:Hng.
    + subst.
      apply np_ng_in in Heq; auto.
Abort.

Lemma nullablePass_add_in :
  forall ps x nu,
    NtSet.In x nu
    -> NtSet.Equal (nullablePass ps nu) (NtSet.add x (nullablePass ps nu)).
Proof.
  intros ps.
  induction ps as [| (x', ys) ps]; intros x nu Hin; simpl in *.
  - fsetdec.
  - destruct (nullableGamma ys (nullablePass ps nu)); auto.
    apply IHps in Hin; fsetdec.
Qed.

Lemma nullableGamma_ret_true :
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

Lemma nullableGamma_ret_eq :
  forall s1 s2 gamma,
    NtSet.Equal s1 s2
    -> nullableGamma gamma s1 = nullableGamma gamma s2.
Proof.
  intros s1 s2 gamma.
  induction gamma as [| sym syms]; intros Heq; simpl in *; auto.
  destruct sym as [y | x]; auto.
  destruct (NtSet.mem x s1) eqn:Hmem; destruct (NtSet.mem x s2) eqn:Hmem'; auto.
  - rewrite NtSet.mem_spec in Hmem.
    apply Heq in Hmem.
    rewrite <- NtSet.mem_spec in Hmem; congruence.
  - rewrite NtSet.mem_spec in Hmem'.
    apply Heq in Hmem'.
    rewrite <- NtSet.mem_spec in Hmem'; congruence.
Qed.

Lemma nullablePass_right_in_left_in :
  forall g x ys suf pre,
    pre ++ suf = g.(productions)
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
      * fsetdec.
      * exfalso.
        eapply nullableGamma_ret_true in Hng; eauto.
        erewrite nullableGamma_ret_eq in Hng; eauto.
        congruence.
    + apply IHsuf with (pre := pre ++ [(x', ys')]); auto.
      * rewrite <- app_assoc; auto. 
      * simpl in *. 
        destruct (nullableGamma ys' (nullablePass suf nu)).
        -- assert (NtSet.In x' nu) by fsetdec. 
           apply nullablePass_add_in with (ps := suf) in H0.
           fsetdec.
        -- auto.
Qed.           

(*
Lemma nullablePass_right_in_left_in :
  forall g x ys,
    In (x, ys) (productions g)
    -> nullable_gamma g ys
    -> forall nu,
        NtSet.Subset(nullablePass (productions g) nu) nu
        -> (forall x, In (NT x) ys -> NtSet.In x nu)
        -> NtSet.In x nu.
Proof.
  intros g x ys Hin Hng.
  induction (productions g) as [| (x', ys') ps]; intros nu Hsub Hall.
  - inv Hin.
  - destruct Hin.
    + inv H; simpl in *.
      destruct (nullableGamma ys (nullablePass ps nu)) eqn:Hf.
      * fsetdec.
      * apply IHps; auto.
    + simpl in *. 
      destruct (nullableGamma ys' (nullablePass ps nu)) eqn:Hf.
      * destruct (NtSetFacts.eq_dec x x').
        -- subst; fsetdec.
        -- apply IHps; auto.
           fsetdec.
Abort.
*)

Lemma eq_complete :
  forall g nu,
    NtSet.Equal nu (nullablePass (productions g) nu)
    -> nullable_set_complete' nu g.
Proof.
  intros g nu Heq.
  unfold nullable_set_complete'.
  intros sym x Hns.
  revert x.
  induction Hns using nullable_sym_mutual_ind with
      (P := fun sym (pf : nullable_sym g sym) =>
              forall x, sym = NT x -> NtSet.In x nu)
      (P0 := fun gamma (pf : nullable_gamma g gamma) =>
               forall x, In (NT x) gamma -> NtSet.In x nu).
  - intros x' Heq'.
    inv Heq'.
    eapply nullablePass_right_in_left_in with 
    (pre := nil); simpl; eauto.
  - intros x Hin.
    inv Hin.
  - intros x Hin.
    destruct Hin.
    + subst.
      apply IHHns; auto.
    + auto.
Qed.

Lemma foo : 
  forall g nu,
    nullable_set_complete (mkNullableSet' (productions g) nu) g
    \/ exists x,
      NtSet.In x (lhSet (productions g))
      /\ ~ NtSet.In x nu
      /\ NtSet.In x (mkNullableSet' (productions g) nu).
Proof.
  intros g nu.
  remember (numRemainingCandidates (productions g) nu) as card.
  generalize dependent nu.
  induction card using lt_wf_ind.
  intros nu Hcard; subst.
  rewrite mkNullableSet'_eq_body; simpl.
  destruct (NtSet.eq_dec nu (nullablePass (productions g) nu)) as [Heq | Hneq].
  - unfold NtSet.eq in Heq. 
    apply eq_complete in Heq.
    left.
    unfold nullable_set_complete.
    unfold nullable_set_complete' in Heq.
    intros x Hns.
    eapply Heq; eauto.
  - destruct (nullablePass_eq_or_candidates_lt (productions g) nu); auto.
    + unfold NtSet.eq in Hneq; congruence.
    + apply H with (nu := nullablePass (productions g) nu) in H0; auto.
      destruct H0.
      * left; auto.
      * right.
        destruct H0 as [x [Hin [Hnin Hin']]].
        exists x.
        split.
        -- auto.
        -- split.
           ++ admit.
           ++ auto.
Admitted.

Lemma mkNullableSet'_complete :
  forall g nu,
    nullable_set_complete (mkNullableSet' (productions g) nu) g.
Proof.
  intros g nu.
Admitted.


Theorem mkNullableSet_complete :
  forall g nu,
    mkNullableSet g = nu
    -> nullable_set_complete nu g.
Proof.
  intros g nu Hmk.
  unfold mkNullableSet in Hmk.
  assert (mkNullableSet' (productions g) nu = nu) by admit.
  pose proof foo.
  destruct (foo g nu).
  - auto.
  - destruct H1 as [x [Hin [Hnin Hin']]].
    rewrite mkNullableSet'_eq_body in H.
    simpl in H.
    destruct (NtSet.eq_dec nu (nullablePass (productions g) nu)).
    + admit.
    + admit.
Qed.