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
  
Lemma foo :
  forall g nu,
    nullable_set_for nu g
    \/ exists x,
      NtSet.In x (lhSet g.(productions))
      /\ ~NtSet.In x nu
      /\ NtSet.In x (nullablePass g.(productions) nu).
Abort.

