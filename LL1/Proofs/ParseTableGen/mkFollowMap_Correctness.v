Require Import List.
Require Import Wf_nat.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Require Import LL1.Proofs.ParseTableGen.mkFirstMap_Correctness.

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

(* Soundness *)

Lemma nullableGamma_nullable_gamma :
  forall g nu x gsuf gpre,
    nullable_set_for nu g
    -> In (x, gpre ++ gsuf) (productions g)
    -> nullableGamma gsuf nu = true
    -> nullable_gamma g gsuf.
Proof.
  intros g nu x gsuf.
  induction gsuf as [| sym gsuf]; intros gpre Hnu Hin Hng; simpl in *.
  - constructor.
  - destruct sym as [y | rx].
    + inv Hng.
    + destruct (NtSet.mem rx nu) eqn:Hmem.
      * rewrite cons_app_singleton in Hin.
        rewrite app_assoc in Hin.
        apply IHgsuf in Hin; clear IHgsuf; auto.
        constructor; auto.
        apply Hnu.
        rewrite <- NtSet.mem_spec; auto.
      * inv Hng.
Qed.
    
Lemma first_gamma_tail_cons :
  forall g la gsuf gpre sym,
    nullable_sym g sym
    -> nullable_gamma g gpre
    -> first_gamma g la gsuf
    -> first_gamma g la (gpre ++ sym :: gsuf).
Proof.
  intros g la gsuf gpre sym Hns Hng Hfg.
  inv Hfg.
  rewrite cons_app_singleton.
  do 2 rewrite app_assoc.
  constructor; auto.
  apply nullable_app; auto.
  apply nullable_app; auto.
Qed.

Lemma firstGamma_first_gamma :
  forall g la nu fi gsuf,
    nullable_set_for nu g
    -> first_map_for fi g
    -> LaSet.In la (firstGamma gsuf nu fi)
    -> first_gamma g la gsuf.
Proof.
  intros g la nu fi gsuf Hnu Hfi Hin.
  induction gsuf as [| sym gsuf]; simpl in *.
  - inv Hin.
  - destruct (nullableSym sym nu) eqn:Hns.
    + apply LaSetFacts.union_1 in Hin.
      destruct Hin as [Hfs | Hfg].
      * rewrite <- app_nil_l.
        constructor.
        -- constructor.
        -- eapply firstSym_first_sym; eauto.
           apply Hfi.
      * apply IHgsuf in Hfg; clear IHgsuf.
        rewrite <- app_nil_l.
        apply first_gamma_tail_cons; auto.
        eapply nullableSym_nullable_sym; eauto.
    + rewrite <- app_nil_l. 
      constructor.
      * constructor.
      * eapply firstSym_first_sym; eauto.
        apply Hfi.
Qed.
    
Lemma first_gamma_firstGamma :
  forall g la nu fi gamma,
    nullable_set_for nu g
    -> first_map_for fi g
    -> first_gamma g la gamma
    -> LaSet.In la (firstGamma gamma nu fi).
Proof.
  intros g la nu fi gamma Hnu Hfi Hfg.
  induction gamma as [| sym syms]; simpl in *.
  - inv Hfg.
    symmetry in H.
    apply app_cons_not_nil in H; inv H.
  - destruct (nullableSym sym nu) eqn:Hns.
    + inv Hfg.
      destruct gpre as [| sym' gpre]; simpl in *.
      * inv H.
        apply LaSetFacts.union_2.
        destruct sym as [y | x]; simpl in *.
        -- congruence.
        -- unfold findOrEmpty.
           destruct Hfi as [Hsou Hcom].
           eapply Hcom in H2.
           destruct H2 as [xFirst [Hf Hin]]; eauto.
           rewrite Hf; auto.
      * inv H.
        apply LaSetFacts.union_3.
        apply IHsyms.
        constructor; auto.
        inv H0; auto.
    + inv Hfg.
      destruct gpre as [| sym' gpre]; simpl in *.
      * inv H.
        destruct sym as [y | x]; simpl in *.
        -- inv H2.
           LD.fsetdec.
        -- unfold findOrEmpty.
           destruct Hfi as [Hsou Hcom].
           eapply Hcom in H2.
           destruct H2 as [xFirst [Hf Hin]]; eauto.
           rewrite Hf; auto.
      * inv H.
        exfalso.
        inv H0.
        eapply nullable_sym_nullableSym in H3; eauto.
        congruence.
Qed.

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
      * destruct (nullableGamma gsuf nu) eqn:Hng.
        -- apply LaSetFacts.union_1 in Hin'.
           destruct Hin' as [Hfe | Hfg].
           ++ apply in_findOrEmpty_exists_set in Hfe.
              destruct Hfe as [lxFollow [Hf_lx Hin_lx]].
              eapply FollowLeft; eauto.
              eapply nullableGamma_nullable_gamma; eauto.
              rewrite cons_app_singleton in Hprod.
              rewrite app_assoc in Hprod.
              eauto.
           ++ eapply FollowRight; eauto.
              eapply firstGamma_first_gamma; eauto.
        -- eapply FollowRight; eauto.
           eapply firstGamma_first_gamma; eauto.
    + rewrite NtMapFacts.add_neq_o in Hf'; auto.
      eapply Hin; eauto.
  - match goal with
    | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
    end; auto.
    destruct (nullableGamma gsuf nu) eqn:Hng.
    + unfold follow_map_sound.
      intros x xFollow la Hf' Hin'.
      destruct (NtSetFacts.eq_dec x rx); subst.
      * apply find_values_eq in Hf'; subst.
        apply LaSetFacts.union_1 in Hin'.
        destruct Hin' as [Hfe | Hfg].
        -- apply in_findOrEmpty_exists_set in Hfe.
           destruct Hfe as [lxFollow [Hf_lx Hin_lx]].
           eapply FollowLeft; eauto.
           eapply nullableGamma_nullable_gamma; eauto.
           rewrite cons_app_singleton in Hprod.
           rewrite app_assoc in Hprod.
           eauto.
        -- eapply FollowRight; eauto.
           eapply firstGamma_first_gamma; eauto.
      * rewrite NtMapFacts.add_neq_o in Hf'; auto.
        eapply Hin; eauto.
    + unfold follow_map_sound.
      intros x xFollow la Hf' Hin'.
      destruct (NtSetFacts.eq_dec x rx); subst.
      * apply find_values_eq in Hf'; subst.
        eapply FollowRight; eauto.
        eapply firstGamma_first_gamma; eauto.
      * rewrite NtMapFacts.add_neq_o in Hf'; auto.
        eapply Hin; eauto.
Qed.

Lemma updateFo_preserves_soundness :
  forall g nu fi lx gamma fo,
    nullable_set_for nu g
    -> first_map_for fi g
    -> In (lx, gamma) (productions g)
    -> follow_map_sound fo g
    -> follow_map_sound (updateFo' nu fi lx gamma fo) g.
Proof.
  intros g nu fi lx gamma fo Hnu Hfi Hin Hfo.
  eapply updateFo_preserves_soundness'; eauto.
  rewrite app_nil_l; auto.
Qed.

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

(* Completeness *)

Lemma ntmap_equiv_refl :
  forall fo,
    NtMap.Equiv LaSet.Equal fo fo.
Proof.
  intros fo.
  unfold NtMap.Equiv.
  split.
  + split; intros; auto.
  + intros k s s' Hmt Hmt'.
    apply NtMapFacts.find_mapsto_iff in Hmt.
    apply NtMapFacts.find_mapsto_iff in Hmt'.
    assert (s = s') by congruence; subst.
    apply LP.equal_refl.
Qed.

Lemma k_in_map_exists_pair :
  forall x m,
    NtMap.In x m
    -> exists la,
      PairSet.In (x, la) (pairsOf m).
Proof.
  intros x m Hin.
  unfold pairsOf.
Admitted.

Lemma mapsto_in_pairsOf :
  forall x s m la,
 NtMap.MapsTo x s m
 -> LaSet.In la s
 -> PairSet.In (x, la) (pairsOf m).
Proof.
  intros x s m la Hmt Hin.
  apply in_findOrEmpty_iff_in_pairsOf.
  unfold findOrEmpty.
  rewrite NtMapFacts.find_mapsto_iff in Hmt.
  rewrite Hmt; auto.
Qed.

Lemma pairsOf_equal_iff_maps_equiv :
  forall m1 m2,
    PairSet.Equal (pairsOf m1) (pairsOf m2)
    <-> NtMap.Equiv LaSet.Equal m1 m2.
Proof.
  intros m1 m2; split; intros Heq.
  - unfold PairSet.Equal in Heq.
    split.
    + intros x; split; intros Hin.
      * (* to do : the values associated with x might be empty in neither or both of the maps; it should be a contradiction if only one is empty *)
        apply k_in_map_exists_pair in Hin.
        destruct Hin as [la Hin].
        apply Heq in Hin.
        eapply in_pairsOf_in_map_keys; eauto.
      * apply k_in_map_exists_pair in Hin.
        destruct Hin as [la Hin].
        apply Heq in Hin.
        eapply in_pairsOf_in_map_keys; eauto.
    + intros x s1 s2 Hmt1 Hmt2.
      unfold LaSet.Equal.
      intros la; split; intros Hin.
      * eapply mapsto_in_pairsOf in Hmt1; eauto.
        apply Heq in Hmt1.
        eapply in_pairsOf_in_set; eauto.
        rewrite <- NtMapFacts.find_mapsto_iff; auto.
      * eapply mapsto_in_pairsOf in Hmt2; eauto.
        apply Heq in Hmt2.
        eapply in_pairsOf_in_set; eauto.
        rewrite <- NtMapFacts.find_mapsto_iff; auto. 
  - unfold PairSet.Equal.
    unfold NtMap.Equiv in Heq.
    destruct Heq as [Hin Hmt].
    intros (x, la); split; intros Hin'.
    + apply in_pairsOf_exists in Hin'.
      destruct Hin' as [s1 [Hmt1 Hin1]].
      pose proof Hmt1 as Hmt1'.
      apply mapsto_in in Hmt1.
      apply Hin in Hmt1.
      apply k_in_map_exists_v in Hmt1.
      destruct Hmt1 as [s2 Hmt2].
      pose proof Hmt2 as Hmt2'.
      eapply Hmt in Hmt2; eauto.
      assert (LaSet.In la s2) by LD.fsetdec.
      eapply find_in_pairsOf; eauto.
      rewrite <- NtMapFacts.find_mapsto_iff; auto.
    + apply in_pairsOf_exists in Hin'.
      destruct Hin' as [s2 [Hmt2 Hin2]].
      pose proof Hmt2 as Hmt2'.
      apply mapsto_in in Hmt2.
      apply Hin in Hmt2.
      apply k_in_map_exists_v in Hmt2.
      destruct Hmt2 as [s1 Hmt1].
      pose proof Hmt1 as Hmt1'.
      eapply Hmt in Hmt1; eauto.
      assert (LaSet.In la s1) by LD.fsetdec.
      eapply find_in_pairsOf; eauto.
      rewrite <- NtMapFacts.find_mapsto_iff; auto.
Qed.

Lemma followPass_equiv_cons_tl :
  forall nu fi fo x gamma ps,
    NtMap.Equiv LaSet.Equal fo
                (followPass ((x, gamma) :: ps) nu fi fo)
    -> NtMap.Equiv LaSet.Equal fo
                   (followPass ps nu fi fo).
Proof.
  intros.
  simpl in *.
  apply pairsOf_equal_iff_maps_equiv.
  apply pairsOf_equal_iff_maps_equiv in H.
  unfold PairSet.Equal in *.
  intros (x', la); split; intros Hin.
  - apply followPass_subset; auto.
  - apply H.
    apply updateFo_subset; auto.
Qed.

Lemma find_updateFo_cons_neq :
  forall x x' nu fi fo lx gsuf xFollow,
  x <> x'
  -> NtMap.find x (updateFo' nu fi lx gsuf fo) = Some xFollow
  -> NtMap.find x (updateFo' nu fi lx (NT x' :: gsuf) fo) = Some xFollow.
Proof.
  intros.
  simpl.
  destruct (NtMap.find (elt:=LaSet.t) x' (updateFo' nu fi lx gsuf fo)) as [x'Follow |].
  - match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
    end; auto.
    rewrite NtMapFacts.add_neq_o; auto.
  - match goal with
    | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
    end; auto.
    rewrite NtMapFacts.add_neq_o; auto.
Qed.

Lemma in_updateFo_cons_neq :
  forall x x' nu fi fo lx gsuf,
  x <> x'
  -> NtMap.In x (updateFo' nu fi lx gsuf fo)
  -> NtMap.In x (updateFo' nu fi lx (NT x' :: gsuf) fo).
Proof.
  intros.
  simpl.
  destruct (NtMap.find (elt:=LaSet.t) x' (updateFo' nu fi lx gsuf fo)) as [x'Follow |].
  - match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
    end; auto.
    rewrite NtMapFacts.add_neq_in_iff; auto.
  - match goal with
    | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
    end; auto.
    rewrite NtMapFacts.add_neq_in_iff; auto.
Qed.

Lemma updateFo_preserves_map_keys :
  forall nu fi fo lx gsuf x sym,
    NtMap.In (elt:=LaSet.t) x (updateFo' nu fi lx gsuf fo)
    ->   NtMap.In (elt:=LaSet.t) x (updateFo' nu fi lx (sym :: gsuf) fo).
Proof.
  intros.
  destruct sym as [y | x']; auto.
  destruct (NtSetFacts.eq_dec x' x); subst.
  - simpl in *.
    destruct (NtMap.find x (updateFo' nu fi lx gsuf fo)) as [xFollow |] eqn:Hf.
    + match goal with
      | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end; auto.
      apply map_key_in_add.
    + exfalso.
      apply k_in_map_exists_v in H.
      destruct H as [s Hmt].
      rewrite NtMapFacts.find_mapsto_iff in Hmt.
      congruence.
  - apply in_updateFo_cons_neq; auto.
Qed.      

Lemma right_nt_is_follow_map_key_first_gamma :
  forall g nu fi fo lx rx gpre gsuf la,
    nullable_set_for nu g
    -> first_map_for fi g
    -> first_gamma g la gsuf
    -> NtMap.In rx (updateFo' nu fi lx (gpre ++ NT rx :: gsuf) fo).
Proof.
  intros.
  induction gpre as [| sym gpre].
  - simpl in *.
    destruct (NtMap.find (elt:=LaSet.t) rx (updateFo' nu fi lx gsuf fo)) as [rxFollow |] eqn:Hf.
    + match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end.
      * destruct (nullableGamma gsuf nu).
        -- eapply ntmap_find_in; eauto.
        -- eapply ntmap_find_in; eauto.
      * apply map_key_in_add.
    + match goal with
      | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
      end.
      * exfalso.
        destruct (nullableGamma gsuf nu).
        -- apply LaSet.is_empty_spec in Hemp.
           assert (LaSet.Empty (firstGamma gsuf nu fi)) by LD.fsetdec.
           eapply first_gamma_firstGamma in H1; eauto.
           LD.fsetdec.
        -- apply LaSet.is_empty_spec in Hemp.
           eapply first_gamma_firstGamma in H1; eauto.
           LD.fsetdec.
      * apply map_key_in_add.
  - apply updateFo_preserves_map_keys; auto.
Qed.
      
Lemma exists_follow_set_containing_first_gamma :
  forall g nu fi fo lx rx gpre gsuf la,
    nullable_set_for nu g
    -> first_map_for fi g
    -> first_gamma g la gsuf
    -> exists rxFollow,
      NtMap.find rx (updateFo' nu fi lx (gpre ++ NT rx :: gsuf) fo) = Some rxFollow
      /\ LaSet.In la rxFollow.
Proof.
  intros.
  induction gpre as [| sym gpre].
  - simpl in *.
    destruct (NtMap.find (elt:=LaSet.t) rx (updateFo' nu fi lx gsuf fo)) as [rxFollow |] eqn:Hf.
    + match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end.
      * destruct (nullableGamma gsuf nu).
        -- exists rxFollow; split; auto.
           apply LaSetFacts.subset_iff in Hsub.
           assert (LaSet.Subset (firstGamma gsuf nu fi) rxFollow) by LD.fsetdec.
           eapply first_gamma_firstGamma in H; eauto.
        -- exists rxFollow; split; auto.
           apply LaSetFacts.subset_iff in Hsub.
           apply Hsub.
           eapply first_gamma_firstGamma; eauto.
      * destruct (nullableGamma gsuf nu).
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ apply LaSetFacts.union_3.
              apply LaSetFacts.union_3.
              eapply first_gamma_firstGamma; eauto.
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ apply LaSetFacts.union_3.
              eapply first_gamma_firstGamma; eauto.
    + match goal with
      | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
      end.
      * destruct (nullableGamma gsuf nu).
        -- exfalso.
           apply LaSet.is_empty_spec in Hemp.
           assert (LaSet.Empty (firstGamma gsuf nu fi)) by LD.fsetdec.
           eapply first_gamma_firstGamma in H1; eauto.
           LD.fsetdec.
        -- apply LaSet.is_empty_spec in Hemp.
           eapply first_gamma_firstGamma in H1; eauto.
           LD.fsetdec.
      * destruct (nullableGamma gsuf nu).
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ apply LaSetFacts.union_3.
              eapply first_gamma_firstGamma; eauto.
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ eapply first_gamma_firstGamma; eauto.
  - destruct sym as [y | rx']; auto.
    destruct IHgpre as [rxFollow [Hf Hin]].
    destruct (NtSetFacts.eq_dec rx' rx); subst.
    + simpl.
      rewrite Hf.
      match goal with
    | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end.
      * destruct (nullableGamma (gpre ++ NT rx :: gsuf) nu); eauto.
      * destruct (nullableGamma (gpre ++ NT rx :: gsuf) nu).
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ apply LaSetFacts.union_2; auto.
        -- eexists; split.
           ++ apply NtMapFacts.add_eq_o; auto.
           ++ apply LaSetFacts.union_2; auto.
    + exists rxFollow; split; auto.
      apply find_updateFo_cons_neq; auto.
Qed.
      
Lemma followPass_equiv_right :
    forall (g : grammar)
           (nu : nullable_set)
           (Hnu : nullable_set_for nu g)
           (fi : first_map)
           (Hfi : first_map_for fi g)
           (fo : follow_map)
           (lx rx : nonterminal)
           (gpre gsuf : list symbol)
           (la : lookahead),
      NtMap.Equiv LaSet.Equal fo (followPass (productions g) nu fi fo)
      -> In (lx, gpre ++ NT rx :: gsuf) (productions g)
      -> first_gamma g la gsuf
      -> exists rxFollow : LaSet.t,
          NtMap.find (elt:=LaSet.t) rx fo = Some rxFollow /\
          LaSet.In la rxFollow.
Proof.
  intros g nu Hnu fi Hfi fo lx rx gpre gsuf la Heq Hin Hfg.
  induction (productions g) as [| (lx', gamma) ps]; simpl in *.
  - inv Hin.
  - destruct Hin; subst.
    + clear IHps.
      inv H.
      destruct Heq as [Hkeys Hmt].
      pose proof (exists_follow_set_containing_first_gamma
                    g nu fi (followPass ps nu fi fo) lx rx gpre gsuf la) as Hex.
      destruct Hex as [rxFollow [Hf Hin]]; auto.
      pose proof Hf as Hf'.
      apply ntmap_find_in in Hf'.
      apply Hkeys in Hf'.
      apply k_in_map_exists_v in Hf'.
      destruct Hf' as [rxFollow' Hmt'].
      rewrite <- NtMapFacts.find_mapsto_iff in Hf.
      pose proof Hmt' as Hmt''.
      rewrite NtMapFacts.find_mapsto_iff in Hmt'.
      eapply Hmt in Hmt''; eauto.
      eexists; split; eauto.
      LD.fsetdec.
    + apply followPass_equiv_cons_tl in Heq.
      eapply IHps; eauto.
Qed.

Lemma followPass_equiv_left :
      forall (g : grammar)
             (nu : nullable_set)
             (Hnu : nullable_set_for nu g)
             (fi : first_map)
             (Hfi : first_map_for fi g)
             (fo : follow_map)
             (lx rx : nonterminal)
             (gpre gsuf : list symbol)
             (la : lookahead)
             (lxFollow : LaSet.t),
        In (lx, gpre ++ NT rx :: gsuf) (productions g)
        -> nullable_gamma g gsuf
        -> NtMap.find (elt:=LaSet.t) lx fo = Some lxFollow
        -> LaSet.In la lxFollow
        -> exists rxFollow : LaSet.t,
            NtMap.find (elt:=LaSet.t) rx fo = Some rxFollow
            /\ LaSet.In la rxFollow.
Proof.
  intros g nu Hnu fi Hfi fo lx rx gpre gsuf la lxFollow Hin Hng Hf_l Hin_l.
Admitted.

Lemma followPass_equiv_complete :
  forall (g : grammar)
         (nu : nullable_set)
         (Hnu : nullable_set_for nu g)
         (fi : first_map)
         (Hfi : first_map_for fi g)
         (fo : follow_map),
    PairSet.In (start g, EOF) (pairsOf fo)
    -> NtMap.Equiv LaSet.Equal fo (followPass (productions g) nu fi fo)
    -> follow_map_complete fo g.
Proof.
  intros g nu Hnu fi Hfi fo Hstart Heq.
  unfold follow_map_complete.
  intros s x la Hfs.
  revert x.
  induction Hfs; intros x' Hs; inv Hs; simpl in *; subst.
  - apply in_pairsOf_exists in Hstart.
    destruct Hstart as [s [Hmt Hin]].
    rewrite NtMapFacts.find_mapsto_iff in Hmt; eauto.
  - eapply followPass_equiv_right; eauto.
  - destruct (IHHfs x1) as [lxFollow [Hf_lx Hin_lx]]; clear IHHfs; auto.
    eapply followPass_equiv_left; eauto.
Qed.
    
Lemma mkFollowMap'_complete :
  forall (g  : grammar)
         (nu : nullable_set)
         (nu_pf : nullable_set_for nu g)
         (fi : first_map)
         (fi_pf : first_map_for fi g)
         (fo : follow_map)
         (fo_pf : all_pairs_are_follow_candidates fo g),
    PairSet.In (start g, EOF) (pairsOf fo)
    -> follow_map_complete (mkFollowMap' g nu fi fi_pf fo fo_pf) g.
Proof.
  intros g nu Hnu fi Hfi fo Hfo Hstart.
  remember (numFollowCandidates g fo) as card.
  generalize dependent fo.
  induction card using lt_wf_ind.
  intros fo Hfo Hstart Hc; subst.
  rewrite mkFollowMap'_eq_body; simpl.
  match goal with 
  | |- context[follow_map_equiv_dec ?fo ?fo'] => 
    destruct (follow_map_equiv_dec fo fo') as [Heq | Hneq]
  end; auto.
  - eapply followPass_equiv_complete; eauto.
  - eapply H; clear H; auto.
    + apply followPass_not_equiv_candidates_lt; auto.
    + apply followPass_subset; auto.
Qed.

Lemma start_eof_in_initial_fo :
  forall g,
    PairSet.In (start g, EOF) (pairsOf (initial_fo g)).
Proof.
  intros g.
  unfold initial_fo.
  apply in_add_keys_eq.
  LD.fsetdec.
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
  unfold mkFollowMap.
  apply mkFollowMap'_complete; auto.
  apply start_eof_in_initial_fo.
Qed.

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
  