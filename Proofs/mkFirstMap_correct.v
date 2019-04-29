Require Import List.
Require Import Wf_nat.

Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Require Import mkNullableSet_correct.

Import ListNotations.

Module FirstProofsFn (G : Grammar.T).

  Module Export NullableProofs := NullableProofsFn G.
  Module Import L              := LemmasFn G.

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
        In (x, gpre ++ gsuf) (prodsOf g)
        -> nullable_gamma g gpre
        -> LaSet.In la (firstGamma gsuf nu fi)
        -> first_sym g la (NT x).
Proof.
  intros g nu fi la x Hns Hfm gsuf.
  induction gsuf as [| sym syms]; intros gpre Hin Hng Hin'; simpl in *.
  - inv Hin'.
  - destruct (nullableSym sym nu) eqn:Hsym.
    + destruct (LaSetFacts.union_1 Hin') as [Hfs | Hfg].
      * apply in_prodsOf_exists_in_xprods in Hin.
        destruct Hin as [f Hin]; econstructor; eauto.
        eapply firstSym_first_sym; eauto.
      * eapply IHsyms with (gpre := gpre ++ [sym]); auto.
        -- rewrite <- app_assoc; auto.
        -- apply nullable_app; auto.
           constructor; auto.
           eapply nullableSym_nullable_sym; eauto.
    + apply in_prodsOf_exists_in_xprods in Hin.
      destruct Hin as [f Hin]; econstructor; eauto.
      eapply firstSym_first_sym; eauto.
Qed.

Lemma firstGamma_first_sym :
  forall g nu fi la x gamma,
    nullable_set_for nu g
    -> first_map_sound fi g
    -> In (x, gamma) (prodsOf g)
    -> LaSet.In la (firstGamma gamma nu fi)
    -> first_sym g la (NT x).
Proof.
  intros.
  eapply firstGamma_first_sym'; eauto.
  simpl; auto.
Qed.

Lemma firstPass_preserves_soundness' :
  forall (g  : grammar)
         (nu : NtSet.t)
         (fi : first_map),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> forall suf pre : list production,
      pre ++ suf = (prodsOf g)
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
         (nu : NtSet.t)
         (fi : first_map),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> first_map_sound (firstPass (prodsOf g) nu fi) g.
Proof.
  intros g nu fi Hns Hfm.
  apply firstPass_preserves_soundness' with (pre := []); eauto.
Qed.

Lemma mkFirstMap'_preserves_soundness :
  forall (g  : grammar)
         (nu : NtSet.t)
         (fi : first_map)
         (pf : all_pairs_are_candidates fi (prodsOf g)),
    nullable_set_for nu g
    -> first_map_sound fi g
    -> first_map_sound (mkFirstMap' (prodsOf g) nu fi pf) g.
Proof.
  intros g nu fi pf Hns Hfm.
  remember (numFirstCandidates (prodsOf g) fi) as card.
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
         (nu : NtSet.t),
    nullable_set_for nu g
    -> first_map_sound (mkFirstMap g nu) g.
Proof.
  intros g nu Hns.
  unfold mkFirstMap.
  apply mkFirstMap'_preserves_soundness; auto.
  apply empty_fi_sound.
Qed.

(* Completeness *)

Lemma mapsto_add_values_eq :
  forall x (s s' : LaSet.t)  m,
    NtMap.MapsTo x s (NtMap.add x s' m)
    -> s = s'.
Proof.
  intros x s s' m Hmt.
  apply NtMapFacts.add_mapsto_iff in Hmt.
  destruct Hmt as [[Heq Heq'] | [Hneq Hmt]]; auto.
  congruence.
Qed.

Lemma equal_in_b_in_a :
  forall (a b : LaSet.t) (la : lookahead),
    LaSet.Equal a b
    -> LaSet.In la b
    -> LaSet.In la a.
Proof.
  LD.fsetdec.
Qed.

(* to do : make this an iff *)
Lemma nullable_sym_nullableSym :
  forall (g : grammar) (nu : NtSet.t) (sym : symbol),
    nullable_set_for nu g
    -> nullable_sym g sym
    -> nullableSym sym nu = true.
Proof.
  intros g nu sym Hset Hsym.
  destruct sym as [y | x]; simpl in *.
  - inv Hsym.
  - destruct Hset as [_ Hcom].
    rewrite NtSet.mem_spec.
    apply Hcom; auto.
Qed.

Lemma la_in_firstGamma_t :
  forall g nu fi y gpre gsuf,
    nullable_set_for nu g
    -> nullable_gamma g gpre
    -> LaSet.In (LA y) (firstGamma (gpre ++ T y :: gsuf) nu fi).
Proof.
  intros g nu fi y gpre gsuf Hns Hng.
  induction gpre as [| sym gpre]; simpl in *.
  - LD.fsetdec.
  - inv Hng.
    erewrite nullable_sym_nullableSym; eauto.
    apply LaSetFacts.union_3; auto.
Qed.

Lemma la_in_firstGamma_nt :
  forall g nu fi x xFirst la gpre gsuf,
    nullable_set_for nu g
    -> nullable_gamma g gpre
    -> NtMap.find x fi = Some xFirst
    -> LaSet.In la xFirst
    -> LaSet.In la (firstGamma (gpre ++ NT x :: gsuf) nu fi).
Proof.
  intros g nu fi x xFirst la gpre gsuf Hns Hng Hf Hin.
  induction gpre as [| sym gpre]; simpl in *.
  - unfold findOrEmpty in *; rewrite Hf in *.
    destruct (NtSet.mem x nu); auto.
    apply LaSetFacts.union_2; auto.
  - inv Hng.
    + erewrite nullable_sym_nullableSym; eauto.
      apply LaSetFacts.union_3; auto.
Qed.

Lemma k_in_map_exists_v :
  forall x (m : NtMap.t LaSet.t),
    NtMap.In x m
    -> exists s,
      NtMap.MapsTo x s m.
Proof.
  intros x m Hin.
  apply NtMapFacts.in_find_iff in Hin.
  destruct (NtMap.find x m) as [s |] eqn:Hf.
  - eexists.
    apply NtMapFacts.find_mapsto_iff; eauto.
  - congruence.
Qed.

Lemma add_k_v_mapsto :
  forall x (s : LaSet.t) m,
    NtMap.MapsTo x s (NtMap.add x s m).
Proof.
  intros x s m.
  apply NtMap.add_1; auto.
Qed.

Lemma equiv_add_exists_equal_v :
  forall m1 m2 x s,
    NtMap.Equiv LaSet.Equal m1 (NtMap.add x s m2)
    -> exists s',
      NtMap.find x m1 = Some s'
      /\ LaSet.Equal s s'.
Proof.
  intros m1 m2 x s Heq.
  destruct Heq as [Hin Hmt].
  specialize (Hin x).
  pose proof map_key_in_add as Hmk.
  apply Hin in Hmk.
  apply k_in_map_exists_v in Hmk.
  destruct Hmk as [s' Hm1].
  pose proof (add_k_v_mapsto x s m2) as Hm2.
  eapply Hmt in Hm2; eauto.
  exists s'; split.
  - apply NtMapFacts.find_mapsto_iff; auto.
  - LD.fsetdec.
Qed.

Lemma firstPass_preserves_map_keys :
  forall x nu fi ps,
    NtMap.In x fi
    -> NtMap.In x (firstPass ps nu fi).
Proof.
  intros x nu fi ps Hin.
  induction ps as [| (x', gamma) ps]; simpl in *; auto.
  match goal with
  | |- context[LaSet.eq_dec ?s ?s'] =>
    destruct (LaSet.eq_dec s s') as [Heq' | Hneq]
  end; auto.
  destruct (NtSetFacts.eq_dec x' x); subst.
  - apply map_key_in_add.
  - apply NtMapFacts.add_neq_in_iff; auto.
Qed.

(* to do : clean this up *)
Lemma value_subset_firstPass :
  forall x nu ps fi xFirst xFirst',
    NtMap.find x fi = Some xFirst
    -> NtMap.find x (firstPass ps nu fi) = Some xFirst'
    -> LaSet.Subset xFirst xFirst'.
Proof.
  intros x nu ps. 
  induction ps as [| (x', gamma) ps]; intros fi xFirst xFirst' Hf Hf'; simpl in *.
  - rewrite Hf in Hf'.
    inv Hf'.
    LD.fsetdec.
  - match goal with
    | H : context[LaSet.eq_dec ?s ?s'] |- _ =>
    destruct (LaSet.eq_dec s s') as [Heq' | Hneq]
    end; eauto.
    destruct (NtSetFacts.eq_dec x' x); subst.
    + pose proof Hf as Hf''.
      apply ntmap_find_in in Hf.
      eapply firstPass_preserves_map_keys with
          (ps := ps)
          (nu := nu) in Hf.
      apply k_in_map_exists_v in Hf.
      destruct Hf as [s Hmt].
      rewrite NtMapFacts.find_mapsto_iff in Hmt.
      unfold findOrEmpty in *; rewrite Hmt in *.
      eapply IHps in Hmt; eauto.
      apply find_values_eq in Hf'.
      subst.
      LD.fsetdec.
    + eapply IHps; eauto.
      rewrite NtMapFacts.add_neq_o in Hf'; auto.
Qed.
  
Lemma firstPass_equiv_cons_tl :
  forall nu x gamma ps fi,
    NtMap.Equiv LaSet.Equal fi
                (firstPass ((x, gamma) :: ps) nu fi)
    -> NtMap.Equiv LaSet.Equal fi
                   (firstPass ps nu fi).
Proof.
  intros nu x gamma suf fi Heq.
  simpl in *.
  match goal with
  | H : context[LaSet.eq_dec ?s ?s'] |- _ =>
    destruct (LaSet.eq_dec s s') as [Heq' | Hneq]
  end; auto.
  exfalso.
  apply Hneq; clear Hneq.
  unfold LaSet.eq.
  apply equiv_add_exists_equal_v in Heq.
  destruct Heq as [xFirst [Hf Heq]].
  pose proof Hf as Hf'.
  apply ntmap_find_in in Hf.
  eapply firstPass_preserves_map_keys in Hf.
  apply k_in_map_exists_v in Hf.
  destruct Hf as [xFirst' Hmt].
  apply NtMapFacts.find_mapsto_iff in Hmt.
  unfold findOrEmpty in *; rewrite Hmt in *.
  eapply value_subset_firstPass in Hmt; eauto.
  LD.fsetdec.
Qed.
      
Lemma firstPass_equiv_right_t' :
  forall g nu lx y gpre gsuf fi psuf,
    In (lx, gpre ++ T y :: gsuf) psuf
    -> nullable_set_for nu g
    -> nullable_gamma g gpre
    -> NtMap.Equiv LaSet.Equal fi (firstPass psuf nu fi)
    -> forall ppre, 
        (prodsOf g) = ppre ++ psuf
        -> exists lxFirst : LaSet.t,
            NtMap.find (elt:=LaSet.t) lx fi = Some lxFirst /\
            LaSet.In (LA y) lxFirst.
Proof.
  intros g nu lx y gpre gsuf fi psuf Hin Hns Hng Hequiv.
  induction psuf as [| (lx', gamma) psuf]; intros ppre Happ; subst; simpl in *.
  - inv Hin.
  - destruct Hin as [Heq | Hin].
    + clear IHpsuf.
      inv Heq.
      match goal with
      | H : context[LaSet.eq_dec ?s ?s'] |- _ =>
        destruct (LaSet.eq_dec s s') as [Heq | Hneq]
      end; auto.
      * unfold LaSet.eq in Heq.
        eapply equal_in_b_in_a with (la := LA y) in Heq.
        -- apply in_findOrEmpty_find_in.
           eapply maps_equiv_in_findOrEmpty; eauto.
        -- apply LaSetFacts.union_2.
           eapply la_in_firstGamma_t; eauto.
      * apply equiv_add_exists_equal_v in Hequiv.
        destruct Hequiv as [lxFirst [Hf Heq]].
        exists lxFirst; split; auto.
        apply Heq.
        apply LaSetFacts.union_2.
        eapply la_in_firstGamma_t; eauto.
    + apply IHpsuf with (ppre := ppre ++ [(lx', gamma)]); auto.
      * eapply firstPass_equiv_cons_tl; eauto.
      * rewrite <- app_assoc; auto.
Qed.

Lemma firstPass_equiv_right_t :
  forall g nu lx y gpre gsuf fi,
    In (lx, gpre ++ T y :: gsuf) (prodsOf g)
    -> nullable_set_for nu g
    -> nullable_gamma g gpre
    -> NtMap.Equiv LaSet.Equal fi (firstPass (prodsOf g) nu fi)
    -> exists lxFirst : LaSet.t,
        NtMap.find (elt:=LaSet.t) lx fi = Some lxFirst /\
        LaSet.In (LA y) lxFirst.
Proof.
  intros.
  eapply firstPass_equiv_right_t'; eauto.
  rewrite app_nil_l; auto.
Qed.

Lemma equiv_in_A_in_B :
  forall x m1 m2,
    NtMap.Equiv LaSet.Equal m1 m2
    -> NtMap.In x m1
    -> NtMap.In x m2.
Proof.
  intros x m1 m2 Heq Hin.
  apply Heq; auto.
Qed.

Lemma equiv_mapsto_values_equal :
  forall x s s' m1 m2,
    NtMap.Equiv LaSet.Equal m1 m2
    -> NtMap.MapsTo x s m1
    -> NtMap.MapsTo x s' m2
    -> LaSet.Equal s s'.
Proof.
  intros x s s' m1 m2 Heq Hmt Hmt'.
  eapply Heq; eauto.
Qed.

Lemma firstPass_equiv_right_nt' :
  forall g nu lx rx rxFirst la gpre gsuf fi psuf,
    In (lx, gpre ++ NT rx :: gsuf) psuf
    -> nullable_set_for nu g
    -> nullable_gamma g gpre
    -> NtMap.Equiv LaSet.Equal fi (firstPass psuf nu fi)
    -> NtMap.find rx fi = Some rxFirst
    -> LaSet.In la rxFirst
    -> forall ppre, 
        (prodsOf g) = ppre ++ psuf
        -> exists lxFirst : LaSet.t,
            NtMap.find (elt:=LaSet.t) lx fi = Some lxFirst /\
            LaSet.In la lxFirst.
Proof.
  intros g nu lx rx rxFirst la gpre gsuf fi psuf Hin Hns Hng Hequiv Hf Hin'.
  induction psuf as [| (lx', gamma) psuf]; intros ppre Happ; subst; simpl in *.
  - inv Hin.
  - destruct Hin as [Heq | Hin].
    + clear IHpsuf.
      inv Heq.
      match goal with
      | H : context[LaSet.eq_dec ?s ?s'] |- _ =>
        destruct (LaSet.eq_dec s s') as [Heq | Hneq]
      end.
      * unfold LaSet.eq in Heq.
        eapply equal_in_b_in_a with (la := la) in Heq.
        -- apply in_findOrEmpty_find_in.
           eapply maps_equiv_in_findOrEmpty; eauto.
        -- apply LaSetFacts.union_2.
           pose proof Hf as Hf'.
           apply ntmap_find_in in Hf.
           pose proof Hequiv as Hequiv'.
           eapply equiv_in_A_in_B in Hequiv; eauto.
           apply k_in_map_exists_v in Hequiv.
           destruct Hequiv as [rxFirst' Hmt].
           rewrite <- NtMapFacts.find_mapsto_iff in Hf'.
           pose proof Hmt as Hmt'.
           eapply equiv_mapsto_values_equal in Hmt; eauto.
           eapply la_in_firstGamma_nt with
               (xFirst := rxFirst'); eauto.
           ++ rewrite <- NtMapFacts.find_mapsto_iff; auto.
           ++ LD.fsetdec.
      * apply equiv_add_exists_equal_v in Hequiv.
        destruct Hequiv as [lxFirst [Hf' Heq]].
        exists lxFirst; split; auto.
        apply Heq.
        apply LaSetFacts.union_2.
        pose proof Hf as Hf''.
        apply ntmap_find_in in Hf.
        apply firstPass_preserves_map_keys with
            (nu := nu)
            (ps := psuf) in Hf.
        apply k_in_map_exists_v in Hf.
        destruct Hf as [rxFirst' Hmt].
        rewrite NtMapFacts.find_mapsto_iff in Hmt.
        eapply la_in_firstGamma_nt; eauto.
        eapply value_subset_firstPass; eauto.
    + apply IHpsuf with (ppre := ppre ++ [(lx', gamma)]); auto.
      * eapply firstPass_equiv_cons_tl; eauto.
      * rewrite <- app_assoc; auto.
Qed.
        
Lemma firstPass_equiv_right_nt :
  forall g nu fi lx rx gpre gsuf rxFirst la,
    nullable_set_for nu g
    -> NtMap.Equiv LaSet.Equal fi (firstPass (prodsOf g) nu fi)
    -> In (lx, gpre ++ NT rx :: gsuf) (prodsOf g)
    -> nullable_gamma g gpre
    -> NtMap.find rx fi = Some rxFirst
    -> LaSet.In la rxFirst
    -> exists lxFirst : LaSet.t,
        NtMap.find (elt:=LaSet.t) lx fi = Some lxFirst /\
        LaSet.In la lxFirst.
Proof.
  intros.
  eapply firstPass_equiv_right_nt'; eauto.
  rewrite app_nil_l; auto.
Qed.

Lemma firstPass_equiv_complete :
  forall g nu fi,
    nullable_set_for nu g
    -> NtMap.Equiv LaSet.Equal fi (firstPass (prodsOf g) nu fi)
    -> first_map_complete fi g.
Proof.
  intros g nu fi Hns Hequiv.
  unfold first_map_complete.
  intros la sym x Hfs.
  revert x.
  induction Hfs; intros lx Heq; inv Heq.
  apply in_xprods_in_prodsOf in H.
  destruct s as [y | rx].
  + inv Hfs.
    clear IHHfs.
    eapply firstPass_equiv_right_t; eauto.
  + specialize (IHHfs rx).
    destruct IHHfs as [rxFirst [Hf Hin]]; auto.
    eapply firstPass_equiv_right_nt; eauto.
Qed.

Lemma mkFirstMap'_complete :
  forall (g  : grammar)
         (nu : NtSet.t)
         (fi : first_map)
         (pf : all_pairs_are_candidates fi (prodsOf g)),
    nullable_set_for nu g
    -> first_map_complete (mkFirstMap' (prodsOf g) nu fi pf) g.
Proof.
  intros g nu fi pf Hns.
  remember (numFirstCandidates (prodsOf g) fi) as card.
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
         (nu : NtSet.t),
    nullable_set_for nu g
    -> first_map_complete (mkFirstMap g nu) g.
Proof.
  intros g nu Hns.
  unfold mkFirstMap.
  apply mkFirstMap'_complete; auto.
Qed.

(* Putting both mkFirstMap correctness properties into a single theorem *)

Theorem mkFirstMap_correct :
  forall (g  : grammar)
         (nu : NtSet.t),
    nullable_set_for nu g
    -> first_map_for (mkFirstMap g nu) g.
Proof.
  intros g nu Hns.
  split.
  - apply mkFirstMap_sound; auto.
  - apply mkFirstMap_complete; auto.
Qed.

End FirstProofsFn.

