Require Import List.
Require Import Wf_nat.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Import ListNotations.

Lemma mkFollowMap'_eq_body :
  forall g nu fi fi_pf fo fo_pf,
  mkFollowMap' g nu fi fi_pf fo fo_pf =
  let fo' := followPass (productions g) nu fi fo in
  if follow_map_equiv_dec fo fo' then
    fo
  else
    mkFollowMap' g nu fi fi_pf fo' (followPass_preserves_apac g nu fi fo fi_pf fo_pf).
Proof.
  intros g nu fi fi_pf fo fo_pf.
  unfold mkFollowMap'.
  unfold mkFollowMap'_func.
  rewrite Wf.fix_sub_eq; auto.
  intros.
  match goal with 
  | |- context[follow_map_equiv_dec ?fo ?fo'] =>
    destruct (follow_map_equiv_dec fo fo') as [Heq | Hneq]
  end; auto.
Qed.

(* found a bug--forgot to check whether gamma tail is nullable! *)
Lemma updateFo_preserves_soundness' :
  forall g nu fi lx fo,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_sound fo g
    -> forall gsuf gpre,
        In (lx, gpre ++ gsuf) (productions g)
    -> follow_map_sound (updateFo' nu fi lx gsuf fo) g.
Proof.
  intros g nu fi lx fo Hnu Hfi Hfo gsuf.
  induction gsuf as [| sym gsuf]; intros gpre Hin; simpl in *; auto.
  pose proof Hin as Hprod.
  rewrite cons_app_singleton in Hin.
  rewrite app_assoc in Hin.
  apply IHgsuf in Hin; clear IHgsuf.
  destruct sym as [y | rx]; auto.
  destruct (NtMap.find rx (updateFo' nu fi lx gsuf fo)) as [rxFollow |] eqn:Hf; auto.
  - match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
    end; auto.
    unfold follow_map_sound.
    intros x xFollow la Hf' Hin'.
    destruct (NtSetFacts.eq_dec x rx); subst.
    + apply find_values_eq in Hf'; subst.
      apply LaSetFacts.union_1 in Hin'.
      destruct Hin' as [Hrxf | Hin'].
      * eapply Hin; eauto.
      * apply LaSetFacts.union_1 in Hin'.
        destruct Hin' as [Hfe | Hfg].
        -- apply in_findOrEmpty_exists_set in Hfe.
           destruct Hfe as [lxFollow [Hf_lx Hin_lx]].
           eapply FollowLeft.
        
      

    
Admitted.

Lemma updateFo_preserves_soundness :
  forall g nu fi lx gamma fo,
    nullable_set_for nu g
    -> first_map_for fi g
    -> In (lx, gamma) (productions g)
    -> follow_map_sound fo g
    -> follow_map_sound (updateFo' nu fi lx gamma fo) g.
Proof.
  intros g nu fi lx gamma fo Hnu Hfi Hin Hfo.
Admitted.

Lemma followPass_preserves_soundness' :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (fo : follow_map),
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_sound fo g
    -> forall suf pre : list production,
        pre ++ suf = (productions g)
        -> follow_map_sound (followPass suf nu fi fo) g.
Proof. 
  intros g nu fi fo Hnu Hfi Hfo suf.
  induction suf as [| (x, gamma) suf]; intros pre Happ; simpl in *; auto.
  pose proof Happ as Happ'.
  rewrite cons_app_singleton in Happ.
  rewrite app_assoc in Happ.
  apply IHsuf in Happ; clear IHsuf.
  apply updateFo_preserves_soundness; auto.
  rewrite <- Happ'.
  apply in_app_cons.
Qed.

Lemma followPass_preserves_soundness :
  forall g nu fi fo,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_sound fo g
    ->  follow_map_sound (followPass (productions g) nu fi fo) g.
Proof.
  intros.
  eapply followPass_preserves_soundness'; eauto.
  rewrite app_nil_l; auto.
Qed.

Lemma mkFollowMap'_preserves_soundness :
  forall (g  : grammar)
         (nu : nullable_set)
         (nu_pf : nullable_set_for nu g)
         (fi : first_map)
         (fi_pf : first_map_for fi g)
         (fo : follow_map)
         (fo_pf : all_pairs_are_follow_candidates fo g),
    follow_map_sound fo g
    -> follow_map_sound (mkFollowMap' g nu fi fi_pf fo fo_pf) g.
Proof.
  intros g nu Hnu fi Hfi fo Hfo Hsou.
  remember (numFollowCandidates g fo) as card.
  generalize dependent fo.
  induction card using lt_wf_ind.
  intros fo Hfo Hsou Hc; subst.
  rewrite mkFollowMap'_eq_body; simpl.
  match goal with 
  | |- context[follow_map_equiv_dec ?fo ?fo'] => 
    destruct (follow_map_equiv_dec fo fo') as [Heq | Hneq]
  end; auto.
  eapply H; clear H; auto.
  - apply followPass_not_equiv_candidates_lt; auto.
  - apply followPass_preserves_soundness; auto.
Qed.

Lemma initial_fo_sound :
  forall g,
    follow_map_sound (initial_fo g) g.
Proof.
  intros g.
  unfold follow_map_sound.
  intros x xFollow la Hf Hin.
  unfold initial_fo in *.
  destruct (NtSetFacts.eq_dec x (start g)); subst.
  - apply find_values_eq in Hf; subst.
    apply LaSetFacts.singleton_1 in Hin; subst.
    apply FollowStart; auto.
  - rewrite NtMapFacts.add_neq_o in Hf; auto.
    inv Hf.
Qed.

Theorem mkFollowMap_sound :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_sound (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
  unfold mkFollowMap.
  apply mkFollowMap'_preserves_soundness; auto.
  apply initial_fo_sound.
Qed.

Theorem mkFollowMap_complete :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_complete (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
Admitted.

Theorem mkFollowMap_correct :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_for (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
  split.
  - apply mkFollowMap_sound; auto.
  - apply mkFollowMap_complete; auto.
Qed.
  