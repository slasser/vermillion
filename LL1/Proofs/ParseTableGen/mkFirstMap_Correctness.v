Require Import Wf_nat.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Lemma mkFirstMap'_eq_body :
  forall ps nu fi pf,
    mkFirstMap' ps nu fi pf =
    let fi' := firstPass ps nu fi in
    if first_map_equiv_dec fi fi' then
      fi
    else
      mkFirstMap' ps nu fi' (firstPass_preserves_apac nu ps fi pf).
Proof.
  intros ps nu fi pf.
  unfold mkFirstMap'.
  unfold mkFirstMap'_func.
  rewrite Wf.fix_sub_eq; auto.
  intros.
  match goal with 
  | |- context[first_map_equiv_dec ?fi ?fi'] =>
    destruct (first_map_equiv_dec fi fi') as [Heq | Hneq]
  end; auto.
Qed.

Lemma firstPass_preserves_soundness :
  forall (g : grammar)
         (nu : nullable_set)
         (fi : first_map),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> first_map_sound (firstPass (productions g) nu fi) g.
Admitted.

Lemma mkFirstMap'_preserves_soundness :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (pf : all_pairs_are_candidates fi (productions g)),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> first_map_sound (mkFirstMap' (productions g) nu fi pf) g.
Proof.
  intros g nu fi pf Hns Hfm.
  remember (numFirstCandidates (productions g) fi) as card.
  generalize dependent fi.
  induction card using lt_wf_ind.
  intros fi pf Hfm Hc; subst.
  rewrite mkFirstMap'_eq_body; simpl.
  match goal with 
  | |- context[first_map_equiv_dec ?fi ?fi'] => 
    destruct (first_map_equiv_dec fi fi') as [Heq | Hneq]
  end; auto.
  eapply H; clear H; eauto.
  - apply firstPass_not_equiv_candidates_lt; auto.
  - apply firstPass_preserves_soundness; auto.
Qed.

Lemma empty_fi_sound :
  forall g,
  first_map_sound empty_fi g.
Proof.
  intros g.
  unfold first_map_sound.
  intros x xFirst la Hf Hin.
  exfalso.
  unfold empty_fi in *.
  pose proof (NtMapFacts.empty_o LaSet.t x).
  congruence.
Qed.

Theorem mkFirstMap_sound :
  forall (g : grammar)
         (nu : nullable_set),
    nullable_set_for nu g
    -> first_map_sound (mkFirstMap g nu) g.
Proof.
  intros g nu Hns.
  unfold mkFirstMap.
  apply mkFirstMap'_preserves_soundness; auto.
  apply empty_fi_sound.
Qed.