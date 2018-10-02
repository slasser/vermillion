Require Import List.
Require Import Wf_nat.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Import ListNotations.

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

Lemma in_findOrEmpty_find_in :
  forall x la fi,
    LaSet.In la (findOrEmpty x fi)
    -> exists s,
      NtMap.find x fi = Some s
      /\ LaSet.In la s.
Proof.
  intros x la fi Hin.
  unfold findOrEmpty in *.
  destruct (NtMap.find x fi) as [s |].
  - eauto.
  - inv Hin.
Qed.

Lemma firstSym_first_sym :
  forall g la sym fi,
    first_map_sound fi g
    -> LaSet.In la (firstSym sym fi)
    -> first_sym g la sym.
Proof.
  intros g la sym fi Hsou Hin.
  destruct sym as [y | x]; simpl in *.
  - apply LaSetFacts.singleton_iff in Hin; subst.
    constructor.
  - apply in_findOrEmpty_find_in in Hin. 
    destruct Hin as [s [Hf Hin]]. 
    eapply Hsou; eauto.
Qed.

Lemma nullable_app :
  forall g xs ys,
    nullable_gamma g xs
    -> nullable_gamma g ys
    -> nullable_gamma g (xs ++ ys).
Proof.
  intros g xs ys Hng Hng'.
  induction xs as [| x xs]; simpl in *; auto.
  inv Hng.
  constructor; auto.
Qed.

Lemma nullableSym_nullable_sym :
  forall g nu sym,
    nullable_set_for nu g
    -> nullableSym sym nu = true
    -> nullable_sym g sym.
Proof.
  intros g nu sym Hns Htr.
  unfold nullableSym in Htr.
  destruct sym as [y | x].
  - inv Htr.
  - apply Hns.
    rewrite <- NtSet.mem_spec; auto.
Qed.

Lemma firstGamma_first_sym' :
  forall g nu fi la x,
    nullable_set_for nu g
    -> first_map_sound fi g
    -> forall gsuf gpre,
        In (x, gpre ++ gsuf) (productions g)
        -> nullable_gamma g gpre
        -> LaSet.In la (firstGamma gsuf nu fi)
        -> first_sym g la (NT x).
Proof.
  intros g nu fi la x Hns Hfm gsuf.
  induction gsuf as [| sym syms]; intros gpre Hin Hng Hin'; simpl in *.
  - inv Hin'.
  - destruct (nullableSym sym nu) eqn:Hsym.
    + destruct (LaSetFacts.union_1 Hin') as [Hfs | Hfg].
      * econstructor; eauto.
        eapply firstSym_first_sym; eauto.
      * eapply IHsyms with (gpre := gpre ++ [sym]); auto.
        -- rewrite <- app_assoc; auto.
        -- apply nullable_app; auto.
           constructor; auto.
           eapply nullableSym_nullable_sym; eauto.
    + econstructor; eauto.
      eapply firstSym_first_sym; eauto.
Qed.

Lemma firstGamma_first_sym :
  forall g nu fi la x gamma,
    nullable_set_for nu g
    -> first_map_sound fi g
    -> In (x, gamma) (productions g)
    -> LaSet.In la (firstGamma gamma nu fi)
    -> first_sym g la (NT x).
Proof.
  intros.
  eapply firstGamma_first_sym'; eauto.
  simpl; auto.
Qed.

Lemma firstPass_preserves_soundness' :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> forall suf pre : list production,
      pre ++ suf = (productions g)
      -> first_map_sound (firstPass suf nu fi) g.
Proof. 
  intros g nu fi Hnf Hfm.
  induction suf as [| (x, gamma) suf]; intros pre Happ; simpl; auto.
  (* todo: write a tactic for this *)
  pose proof Happ as Happ'.
  rewrite cons_app_singleton in Happ.
  rewrite app_assoc in Happ.
  apply IHsuf in Happ; clear IHsuf.
  match goal with 
  | |- context[LaSet.eq_dec ?s ?s'] => 
    destruct (LaSet.eq_dec s s') as [Heq | Hneq]
  end; auto.
  unfold first_map_sound.
  intros x' xFirst la Hf Hin.
  destruct (NtSetFacts.eq_dec x' x); subst.
  - clear Hneq.
    apply find_values_eq in Hf; subst.
    destruct (LaSetFacts.union_1 Hin) as [Hfg | Hfe]; auto.
    + eapply firstGamma_first_sym; eauto.
      rewrite <- Happ'.
      apply in_app_cons.
    + apply in_findOrEmpty_find_in in Hfe. 
      destruct Hfe as [s [Hf Hin']]; eauto.
  - rewrite NtMapFacts.add_neq_o in Hf; eauto.
Qed.
    
Lemma firstPass_preserves_soundness :
  forall (g : grammar)
         (nu : nullable_set)
         (fi : first_map),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> first_map_sound (firstPass (productions g) nu fi) g.
Proof.
  intros g nu fi Hns Hfm.
  apply firstPass_preserves_soundness' with (pre := []); eauto.
Qed.

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

(* Completeness *)

Lemma firstPass_equiv_complete :
  forall g nu fi,
    NtMap.Equiv LaSet.Equal fi (firstPass (productions g) nu fi)
    -> first_map_complete fi g.
Proof.
  intros g nu fi Hequiv.
  unfold first_map_complete.
  intros la sym x Hfs.
  revert x.
  induction Hfs; intros lx Heq; inv Heq.
  destruct s as [y | rx].
  + inv Hfs.
    clear IHHfs.
    admit.
  + specialize (IHHfs rx).
    destruct IHHfs as [rxFirst [Hf Hin]]; auto.
Admitted.

Lemma mkFirstMap'_complete :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (pf : all_pairs_are_candidates fi (productions g)),
    nullable_set_for nu g
    -> first_map_complete (mkFirstMap' (productions g) nu fi pf) g.
Proof.
  intros g nu fi pf Hns.
  remember (numFirstCandidates (productions g) fi) as card.
  generalize dependent fi.
  induction card using lt_wf_ind.
  intros fi pf Hc; subst.
  rewrite mkFirstMap'_eq_body; simpl.
  match goal with 
  | |- context[first_map_equiv_dec ?fi ?fi'] => 
    destruct (first_map_equiv_dec fi fi') as [Heq | Hneq]
  end.
  - eapply firstPass_equiv_complete; eauto.
  - eapply H; clear H; eauto.
    apply firstPass_not_equiv_candidates_lt; auto.
Qed.

Theorem mkFirstMap_complete :
  forall (g : grammar)
         (nu : nullable_set),
    nullable_set_for nu g
    -> first_map_complete (mkFirstMap g nu) g.
Proof.
  intros g nu Hns.
  unfold mkFirstMap.
  apply mkFirstMap'_complete; auto.
Qed.

