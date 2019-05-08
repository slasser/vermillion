Require Import List.
Require Import MSets.
Require Import Program.Wf.
Require Import String.

Require Import Vermillion.Grammar.
Require Import Vermillion.Lemmas.
Require Import Vermillion.Tactics.

Import ListNotations.
Open Scope string_scope.

Module GeneratorFn (Export G : Grammar.T).

  Module Import L := LemmasFn G.
  
  (* Step 1 in the table generation pipeline: compute the NULLABLE set for a grammar *)
  
  Definition lhSet (ps : list production) : NtSet.t :=
    fromNtList (map fst ps).
  
  Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
    match gamma with 
    | [] => true
    | T _ :: _ => false
    | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
    end.
  
  Definition updateNu (p : production) (nu : NtSet.t) : NtSet.t :=
    let (x, gamma) := p in
    if nullableGamma gamma nu then
      NtSet.add x nu
    else
      nu.

  Definition nullablePass (ps : list production) (nu : NtSet.t) : NtSet.t :=
    fold_right updateNu nu ps.
  
  Lemma subset_subset_diffs :
    forall a b c : NtSet.t,
      NtSet.Subset a b
      -> NtSet.Subset (NtSet.diff c b) (NtSet.diff c a).
  Proof.
    ND.fsetdec.
  Defined.
  
  Lemma nullablePass_subset :
    forall ps nu,
      NtSet.Subset nu (nullablePass ps nu).
  Proof.
    induction ps as [| p ps]; intros nu; simpl in *; try ND.fsetdec.
    unfold updateNu.
    destruct p as (x, gamma).
    destruct (nullableGamma gamma (nullablePass ps nu)); auto.
    apply NtSetEqProps.MP.subset_add_2; auto.
  Defined.
  
  Lemma In_lhSet_cons :
    forall x' ps x gamma,
      NtSet.In x' (lhSet ps)
      -> NtSet.In x' (lhSet ((x, gamma) :: ps)).
  Proof.
    intros.
    unfold lhSet in *; simpl in *; ND.fsetdec.
  Defined.
  
  Lemma nullablePass_eq_or_exists :
    forall ps nu,
      NtSet.Equal nu (nullablePass ps nu)
      \/ exists x,
        NtSet.In x (lhSet ps)
        /\ ~NtSet.In x nu
        /\ NtSet.In x (nullablePass ps nu).
  Proof.
    induction ps as [| (x, gamma) ps]; intros nu; simpl in *; try ND.fsetdec.
    destruct (nullableGamma gamma (nullablePass ps nu)).
    - destruct (NtSetEqProps.MP.In_dec x nu).
      + destruct (IHps nu).
        * left; ND.fsetdec.
        * destruct H as [x' [Hin [Hnin Hin']]].
          right; eexists; repeat split; eauto.
          -- apply In_lhSet_cons; auto.
          -- ND.fsetdec.
      + right; eexists; repeat split; eauto; try ND.fsetdec.
        unfold lhSet; simpl; ND.fsetdec.
    - destruct (IHps nu); auto.
      destruct H as [x' [Hin [Hnin Hin']]].
      right; eexists; split; eauto.
      apply In_lhSet_cons; auto.
  Defined.
  
  Lemma nullablePass_neq_exists :
    forall ps nu,
      ~ NtSet.Equal nu (nullablePass ps nu)
      -> exists x,
        NtSet.In x (lhSet ps)
        /\ ~ NtSet.In x nu
        /\ NtSet.In x (nullablePass ps nu).
  Proof.
    intros ps nu Hneq.
    destruct (nullablePass_eq_or_exists ps nu); congruence.
  Defined.
  
  Definition countNullableCandidates (ps : list production) (nu : NtSet.t) : nat :=
    let candidates := lhSet ps in
    NtSet.cardinal (NtSet.diff candidates nu).
  
  Lemma nullablePass_neq_candidates_lt :
    forall ps nu,
      ~ NtSet.Equal nu (nullablePass ps nu)
      -> countNullableCandidates ps (nullablePass ps nu) < countNullableCandidates ps nu.
  Proof.
    intros ps nu Hneq.
    apply nullablePass_neq_exists in Hneq.
    firstorder.
    apply NtSetEqProps.MP.subset_cardinal_lt with (x := x); try ND.fsetdec.
    apply subset_subset_diffs.
    apply nullablePass_subset.
  Defined.
  
  Program Fixpoint mkNullableSet' 
          (ps : list production) 
          (nu : NtSet.t)
          { measure (countNullableCandidates ps nu) }:=
    let nu' := nullablePass ps nu in
    if NtSet.eq_dec nu nu' then
      nu
    else
      mkNullableSet' ps nu'.
  Next Obligation.
    apply nullablePass_neq_candidates_lt; auto.
  Defined.
  
  Definition mkNullableSet (g : grammar) : NtSet.t :=
    mkNullableSet' (prodsOf g) NtSet.empty.
  
  (* Step 2 : compute the FIRST map for the grammar 
     using the (correct) NULLABLE set. *)

  Definition nullableSym (sym : symbol) (nu : NtSet.t) := 
    match sym with
    | T _  => false
    | NT x => NtSet.mem x nu
    end.
  
  Definition findOrEmpty (x : nonterminal) (fi : first_map) : LaSet.t :=
    match NtMap.find x fi with
    | Some s => s
    | None => LaSet.empty
    end.
  
  Definition firstSym (sym : symbol) (fi : first_map) : LaSet.t :=
    match sym with
    | T y => LaSet.singleton (LA y)
    | NT x => findOrEmpty x fi
    end.
  
  (* Compute the set of lookahead tokens for gamma using correct NULLABLE set nu
   and possibly incomplete FIRST map fi *)
  Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :=
    match gamma with
    | [] => LaSet.empty
    | sym :: gamma' =>
      if nullableSym sym nu then
        LaSet.union (firstSym sym fi) (firstGamma gamma' nu fi)
      else firstSym sym fi
    end.
  
  Definition updateFi (nu : NtSet.t) (p : production) (fi : first_map) : first_map :=
    let (x, gamma) := p in
    let fg := firstGamma gamma nu fi in
    let xFirst := findOrEmpty x fi in
    let xFirst' := LaSet.union fg xFirst in
    if LaSet.eq_dec xFirst xFirst' then (* necessary? *)
      fi
    else
      NtMap.add x xFirst' fi.

  Definition firstPass (ps : list production) (nu : NtSet.t) (fi : first_map) : first_map :=
    fold_right (updateFi nu) fi ps.

  Definition first_map_equiv_dec :
    forall m m' : first_map,
      {NtMap.Equiv LaSet.Equal m m'} + {~ NtMap.Equiv (LaSet.Equal) m m'}.
  Proof.
    intros m m'.
    destruct (NtMap.equal (LaSet.equal) m m') eqn:Heq.
    - left.
      apply NtMapFacts.equal_iff in Heq.
      rewrite <- NtMapFacts.Equiv_Equivb with
          (eq_elt := LaSet.Equal) in Heq; auto.
      unfold NtMapFacts.compat_cmp.
      intros s s'.
      rewrite LaSet.equal_spec; split; auto.
    - right.
      unfold not; intros.
      rewrite NtMapFacts.Equiv_Equivb in H.
      + pose proof (NtMapFacts.equal_iff m m' LaSet.equal).
        apply H0 in H.
        congruence.
      + unfold NtMapFacts.compat_cmp.
        intros s s'.
        rewrite LaSet.equal_spec; split; auto.
  Defined.
  
  Definition nt_la_pair := (nonterminal * lookahead)%type.
  
  Definition pair_eq_dec :
    forall (p p' : nt_la_pair),
      {p = p'} + {~ p = p'}.
  Proof. repeat decide equality. Defined.
  
  Module MDT_Pair.
    Definition t := nt_la_pair.
    Definition eq_dec := pair_eq_dec.
  End MDT_Pair.
  
  Module Pair_as_DT := Make_UDT(MDT_Pair).
  Module PairSet := MSetWeakList.Make Pair_as_DT.
  Module PairSetFacts := WFactsOn Pair_as_DT PairSet.
  Module PairSetEqProps := EqProperties PairSet.
  
  Module PP := MSetProperties.Properties PairSet.
  Module PD := WDecideOn Pair_as_DT PairSet.
  
  Definition mkPairs (x : nonterminal) (laSet : LaSet.t) :=
    fold_right (fun la acc => PairSet.add (x, la) acc) PairSet.empty (LaSet.elements laSet).
  
  Definition pairsOf (fi : first_map) : PairSet.t := 
    fold_right (fun p acc => 
                  match p with
                  | (x, s) => PairSet.union (mkPairs x s) acc
                  end) PairSet.empty (NtMap.elements fi).
  
  Fixpoint leftmostLookahead (gamma : list symbol) :=
    match gamma with 
    | [] => None
    | T y :: _ => Some (LA y)
    | NT _ :: gamma' => leftmostLookahead gamma'
    end.
  
  Definition leftmostLookaheads' (gammas : list (list symbol)) : LaSet.t :=
    fold_right (fun gamma acc => 
                  match leftmostLookahead gamma with
                  | Some la => LaSet.add la acc
                  | None => acc
                  end) LaSet.empty gammas.
  
  Definition leftmostLookaheads (ps : list production) :=
    leftmostLookaheads' (map snd ps).
  
  Definition product (n : NtSet.t) (l : LaSet.t) : PairSet.t :=
    let f := (fun x acc => PairSet.union (mkPairs x l) acc) in
    NtSet.fold f n PairSet.empty.
  
  Definition numFirstCandidates (ps : list production) (fi : first_map) :=
    let allCandidates := product (lhSet ps) (leftmostLookaheads ps) in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fi)).
  
  (* get rid of this duplication *)
  Lemma pairset_subset_subset_diffs :
    forall a b c : PairSet.t,
      PairSet.Subset a b 
      -> PairSet.Subset (PairSet.diff c b) (PairSet.diff c a).
  Proof.
    PD.fsetdec.
  Defined.
  
  Lemma ps_in_A_not_in_B_in_diff :
    forall elt a b,
      PairSet.In elt a
      -> ~ PairSet.In elt b
      -> PairSet.In elt (PairSet.diff a b).
  Proof.
    PD.fsetdec.
  Defined.
  
  Lemma in_elements_iff_in_laSet :
    forall la s,
      In la (LaSet.elements s) <-> LaSet.In la s.
  Proof.
    intros la s.
    split; intros Hin.
    - apply LaSetFacts.elements_iff.
      apply SetoidList.In_InA; auto.
    - rewrite LaSetFacts.elements_iff in Hin.
      apply SetoidList.InA_alt in Hin.
      destruct Hin as [la' [Heq Hin]].
      subst; auto.
  Defined.

  Lemma in_elements_iff_in_ntSet :
    forall x s,
      In x (NtSet.elements s) <-> NtSet.In x s.
  Proof.
    intros x s.
    split; intros Hin.
    - apply NtSetFacts.elements_iff.
      apply SetoidList.In_InA; auto.
    - rewrite NtSetFacts.elements_iff in Hin.
      apply SetoidList.InA_alt in Hin.
      destruct Hin as [x' [Heq Hin]].
      subst; auto.
  Defined.
  
  Lemma in_set_in_mkPairs' :
    forall (x   : nonterminal)
           (la  : lookahead)
           (las : list lookahead),
      In la las
      -> PairSet.In (x, la)
                    (fold_right (fun la acc => PairSet.add (x, la) acc) 
                                PairSet.empty 
                                las).
  Proof.
    intros x la las Hin.
    induction las as [| la' las]; simpl in *.
    - inv Hin.
    - destruct Hin; subst; try PD.fsetdec.
      apply IHlas in H; PD.fsetdec.
  Defined.
  
  Lemma in_set_in_mkPairs :
    forall (x  : nonterminal)
           (la : lookahead)
           (s  : LaSet.t),
      LaSet.In la s
      -> PairSet.In (x, la) (mkPairs x s).
  Proof.
    intros x la s Hin.
    unfold mkPairs.
    apply in_set_in_mkPairs'.
    apply in_elements_iff_in_laSet; auto.
  Defined.
  
  Lemma in_A_in_B_in_product' :
    forall (x : nonterminal)
           (xs : list nonterminal)
           (la : lookahead)
           (s  : LaSet.t),
      In x xs
      -> LaSet.In la s
      -> PairSet.In (x, la)
                    (fold_right (fun x acc => PairSet.union (mkPairs x s) acc) 
                                PairSet.empty 
                                xs).
  Proof.
    intros x xs.
    induction xs as [| x' xs]; intros la s Hin Hin'; simpl in *.
    - inv Hin.
    - destruct Hin; subst.
      + apply in_set_in_mkPairs with (x := x) in Hin'. 
        PD.fsetdec.
      + eapply IHxs in H; eauto.
        PD.fsetdec.
  Defined.
  
  Lemma in_A_in_B_in_product :
    forall x la ntSet laSet,
      NtSet.In x ntSet
      -> LaSet.In la laSet
      -> PairSet.In (x, la) (product ntSet laSet).
  Proof.
    intros x la ntSet laSet Hin Hin'.
    unfold product.
    rewrite NP.fold_spec_right.
    apply in_A_in_B_in_product'; auto.
    rewrite <- in_rev.
    apply in_elements_iff_in_ntSet; auto.
  Defined.

  Lemma in_leftmostLookaheads_cons :
    forall la p ps,
      LaSet.In la (leftmostLookaheads ps)
      -> LaSet.In la (leftmostLookaheads (p :: ps)).
  Proof.
    intros la (x, gamma) ps Hin.
    unfold leftmostLookaheads in *.
    induction ps as [| (x', gamma') ps]; simpl in *.
    - inv Hin.
    - destruct (leftmostLookahead gamma) as [la' |]; 
        destruct (leftmostLookahead gamma') as [la'' |]; auto; LD.fsetdec.
  Defined.
  
  Definition all_pairs_are_candidates (fi : first_map) (ps : list production) :=
    forall x la,
      PairSet.In (x, la) (pairsOf fi)
      -> NtSet.In x (lhSet ps)
         /\ LaSet.In la (leftmostLookaheads ps).
 
  
  Definition all_nt (gamma : list symbol) :=
    Forall (fun sym => isNT sym = true) gamma.

  Lemma gpre_nullable_leftmost_lk_some :
    forall gpre y gsuf,
      all_nt gpre
      -> leftmostLookahead (gpre ++ T y :: gsuf) = Some (LA y).
  Proof.
    intros gpre y gsuf Han.
    induction gpre as [| sym gpre]; simpl in *; auto.
    destruct sym as [y' | x].
    - inv Han.
      inv H1. (* LEMMA *)
    - apply IHgpre.
      inv Han; auto.
  Defined.

  Lemma gpre_nullable_in_leftmost_lks :
    forall x y gpre gsuf ps,
      In (x, gpre ++ T y :: gsuf) ps
      -> all_nt gpre
      -> LaSet.In (LA y) (leftmostLookaheads ps).
  Proof.
    intros x y gpre gsuf ps Hin Han.
    induction ps as [| (x', gamma) ps]; simpl in *.
    - inv Hin.
    - destruct Hin.
      + inv H.
        unfold leftmostLookaheads; simpl.
        rewrite gpre_nullable_leftmost_lk_some; auto.
        LD.fsetdec.
      + apply IHps in H.
        apply in_leftmostLookaheads_cons; auto.
  Defined.
  
  Lemma Forall_app :
    forall A (P : A -> Prop) (xs ys : list A),
      Forall P xs
      -> Forall P ys
      -> Forall P (xs ++ ys).
  Proof.
    intros A P xs.
    induction xs as [| x xs]; intros ys Hf Hf'; simpl in *; auto.
    - inv Hf. 
      constructor; auto.
  Defined.

  Lemma find_in :
    forall x (s : LaSet.t) fi,
      NtMap.find x fi = Some s
      -> In (x, s) (NtMap.elements fi).
  Proof.
    intros.
    rewrite NtMapFacts.elements_o in H.
    induction (NtMap.elements fi) as [| (x', s')]; simpl in *.
    - inv H.
    - unfold NtMapFacts.eqb in *. 
      destruct (NtSetFacts.eq_dec x x'); subst; auto.
      inv H; auto.
  Defined.

  Lemma in_A_in_B_in_pairsOf :
    forall x la s fi,
      In (x, s) (NtMap.elements fi) 
      -> LaSet.In la s
      -> PairSet.In (x, la) (pairsOf fi).
  Proof.
    intros x la s fi Hf Hin.
    unfold pairsOf.
    induction (NtMap.elements fi) as [| (x', s')]; simpl in *.
    - inv Hf.
    - destruct Hf.
      + inv H.
        apply PairSetFacts.union_2.
        apply in_set_in_mkPairs; auto.
      + apply PairSetFacts.union_3; auto.
  Defined.
  
  Lemma in_firstGamma_in_leftmost_lks' :
    forall nu ps la fi x gsuf gpre,
      In (x, gpre ++ gsuf) ps
      -> all_pairs_are_candidates fi ps
      -> all_nt gpre
      -> LaSet.In la (firstGamma gsuf nu fi)
      -> LaSet.In la (leftmostLookaheads ps).
  Proof.
    intros nu ps la fi x gsuf.
    induction gsuf as [| sym gsuf]; intros gpre Hin Hapac Hfa Hin'; simpl in *.
    - inv Hin'.
    - destruct sym as [y | x']; simpl in *.
      + apply LaSet.singleton_spec in Hin'; subst.
        eapply gpre_nullable_in_leftmost_lks; eauto.
      + destruct (NtSet.mem x' nu). 
        * apply LaSetFacts.union_1 in Hin'. 
          destruct Hin'. 
          -- unfold findOrEmpty in H.
             destruct (NtMap.find x' fi) as [x'First |] eqn:Hf.
             ++ eapply Hapac.
                apply find_in in Hf.
                eapply in_A_in_B_in_pairsOf; eauto.
             ++ inv H.
          -- apply IHgsuf with (gpre := gpre ++ [NT x']); auto.
             ++ rewrite <- app_assoc; auto.
             ++ apply Forall_app; auto.
        * unfold findOrEmpty in Hin'.
          destruct (NtMap.find x' fi) as [x'First |] eqn:Hf.
          ++ eapply Hapac.
             eapply in_A_in_B_in_pairsOf; eauto.
             apply find_in; eauto.
          ++ inv Hin'.
  Defined.

  Lemma in_firstGamma_in_leftmost_lks :
    forall nu ps la fi x gamma,
      In (x, gamma) ps
      -> all_pairs_are_candidates fi ps
      -> LaSet.In la (firstGamma gamma nu fi)
      -> LaSet.In la (leftmostLookaheads ps).
  Proof.
    intros.
    eapply in_firstGamma_in_leftmost_lks' with (gpre := []); simpl; eauto.
    constructor.
  Defined.
  
  Definition list_subset A (xs xs' : list A) :=
    forall x, In x xs -> In x xs'.
  
  Definition list_equal A (xs xs' : list A) :=
    forall x, In x xs <-> In x xs'.
  
  Lemma list_subset_neq_exists_elt :
    forall A xs xs'
           (eq_dec : forall x x' : A, {x = x'} + {x <> x'}),
      list_subset A xs xs'
      -> ~ list_equal A xs xs'
      -> exists x',
          In x' xs'
          /\ ~ In x' xs.
  Proof.
    intros A xs xs' Heq Hsub Hneq.
    assert (~ ((list_subset A xs xs') /\ (list_subset A xs' xs))) by firstorder.
    assert (~ (list_subset A xs' xs)) by firstorder.
    assert (~ Forall (fun x => In x xs) xs'). (* LEMMA *)
    { unfold not; intros.
      apply H0.
      unfold list_subset.
      apply Forall_forall; auto. }
    apply Exists_Forall_neg in H1.
    - apply Exists_exists; auto.
    - intros x.
      destruct (in_dec Heq x xs); auto.
  Defined.

  Lemma subset_list_subset :
    forall s s',
      LaSet.Subset s s'
      -> list_subset LaSet.elt (LaSet.elements s) (LaSet.elements s').
  Proof.
    intros s s' Hsub.
    unfold LaSet.Subset in *.
    unfold list_subset.
    intros x Hin.
    apply in_elements_iff_in_laSet.
    apply Hsub.
    apply in_elements_iff_in_laSet.
    auto.
  Defined.
  
  Lemma not_equal_not_list_equal :
    forall s s',
      ~ LaSet.Equal s s'
      -> ~ list_equal LaSet.elt (LaSet.elements s) (LaSet.elements s').
  Proof.
    intros s s' Hneq.
    unfold not; intros.
    apply Hneq.
    unfold LaSet.Equal, list_equal in *.
    intros x; split; intros Hin.
    - apply in_elements_iff_in_laSet.
      apply H.
      apply in_elements_iff_in_laSet.
      auto.
    - apply in_elements_iff_in_laSet.
      apply H.
      apply in_elements_iff_in_laSet.
      auto.
  Defined.

  Lemma exists_list_elt_exists_set_elt :
    forall s s',
      (exists la, In la (LaSet.elements s')
                  /\ ~ In la (LaSet.elements s))
      -> exists la, LaSet.In la s'
                    /\ ~ LaSet.In la s.
  Proof.
    intros s s' Hex.
    destruct Hex as [la [Hin Hnin]].
    exists la; split.
    - apply in_elements_iff_in_laSet; auto.
    - unfold not; intros.
      apply Hnin.
      apply in_elements_iff_in_laSet; auto.
  Defined.
  
  Lemma subset_neq_exists_elt :
    forall s s',
      LaSet.Subset s s'
      -> ~ LaSet.Equal s s'
      -> exists la,
          LaSet.In la s'
          /\ ~ LaSet.In la s.
  Proof.
    intros s s' Hsub Hneq.
    apply subset_list_subset in Hsub.
    apply not_equal_not_list_equal in Hneq.
    apply exists_list_elt_exists_set_elt.
    apply list_subset_neq_exists_elt; auto.
    apply lookahead_eq_dec.
  Defined.    
  
  Lemma union_neq_exists_elt :
    forall s s',
      ~ LaSet.Equal s (LaSet.union s' s)
      -> exists la,
        LaSet.In la s'
        /\ ~ LaSet.In la s.
  Proof.
    intros.
    apply subset_neq_exists_elt in H; auto; try LD.fsetdec.
    destruct H as [la [Hin Hnin]].
    assert (LaSet.In la s') by LD.fsetdec.
    exists la; split; auto.
  Defined.
  
  Lemma in_lhSet_app :
    forall x gamma pre suf,
      NtSet.In x (lhSet (pre ++ (x, gamma) :: suf)).
  Proof.
    intros.
    induction pre as [| (x', gamma')]; unfold lhSet; simpl in *.
    - ND.fsetdec.
    - apply NtSetFacts.add_2.
      auto.
  Defined.
  
  Lemma ntmap_find_in : forall k vT (v : vT) m,
      NtMap.find k m = Some v
      -> NtMap.In k m.
  Proof.
    intros. rewrite NtMapFacts.in_find_iff. rewrite H.
    unfold not. intro Hcontra. inv Hcontra.
  Defined.
  
  Lemma maps_equiv_in_findOrEmpty :
    forall fi fi' x la,
      NtMap.Equiv LaSet.Equal fi fi'
      -> LaSet.In la (findOrEmpty x fi')
      -> LaSet.In la (findOrEmpty x fi).
  Proof.
    intros fi fi' x la Heq Hin.
    destruct Heq as [Hin' Hmt].
    unfold findOrEmpty in *.
    destruct (NtMap.find x fi) as [s |] eqn:Hf;
      destruct (NtMap.find x fi') as [s' |] eqn:Hf'.
    - apply NtMapFacts.find_mapsto_iff in Hf.
      apply NtMapFacts.find_mapsto_iff in Hf'.
      eapply Hmt in Hf; eauto.
      LD.fsetdec.
    - apply ntmap_find_in in Hf.
      apply Hin' in Hf.
      apply NtMapFacts.in_find_iff in Hf.
      congruence.
    - apply ntmap_find_in in Hf'.
      apply Hin' in Hf'.
      apply NtMapFacts.in_find_iff in Hf'.
      congruence.
    - inv Hin.
  Defined.
  
  Lemma maps_equiv_not_in_findOrEmpty :
    forall fi fi' x la,
      NtMap.Equiv LaSet.Equal fi fi'
      -> ~ LaSet.In la (findOrEmpty x fi)
      -> ~ LaSet.In la (findOrEmpty x fi').
  Proof.
    intros fi fi' x la Heq Hnin.
    unfold not; intros Hin.
    apply Hnin.
    eapply maps_equiv_in_findOrEmpty; eauto.
  Defined.

  Lemma maps_equiv_in_firstSym_iff :
    forall fi fi' la sym,
      NtMap.Equiv LaSet.Equal fi fi'
      -> LaSet.In la (firstSym sym fi')
      -> LaSet.In la (firstSym sym fi).
  Proof.
    intros fi fi' la sym Heq Hin.
    destruct sym as [y | x]; simpl in *; auto.
    eapply maps_equiv_in_findOrEmpty; eauto.
  Defined.
  
  Lemma maps_equiv_in_firstGamma_iff :
    forall nu fi fi' la gamma,
      NtMap.Equiv LaSet.Equal fi fi'
      -> LaSet.In la (firstGamma gamma nu fi')
      -> LaSet.In la (firstGamma gamma nu fi).
  Proof.
    intros nu fi fi' la gamma Heq Hin.
    induction gamma as [| sym gamma]; simpl in *.
    - inv Hin.
    - destruct (nullableSym sym nu).
      + eapply LaSetFacts.union_1 in Hin.
        destruct Hin as [Hfs | Hfg].
        * apply LaSetFacts.union_2.
          eapply maps_equiv_in_firstSym_iff; eauto.
        * apply LaSetFacts.union_3.
          apply IHgamma; auto.
      + eapply maps_equiv_in_firstSym_iff; eauto.
  Defined.
  
  Lemma in_mkPairs_in_set' :
    forall x la las,
      PairSet.In (x, la)
                 (fold_right (fun la acc => PairSet.add (x, la) acc)
                             PairSet.empty
                             las)
      -> In la las.
  Proof.
    intros x la las Hin.
    induction las as [| la' las]; simpl in *.
    - inv Hin.
    - destruct (lookahead_eq_dec la' la); subst; auto.
      right.
      apply IHlas.
      eapply PairSetFacts.add_3; eauto.
      congruence.
  Defined.
  
  Lemma mkPairs_keys_eq :
    forall x x' la s,
      PairSet.In (x, la) (mkPairs x' s)
      -> x = x'.
  Proof.
    intros x x' la s Hin.
    unfold mkPairs in *.
    induction (LaSet.elements s) as [| la' elts]; simpl in *.
    - inv Hin.
    - destruct (NtSetFacts.eq_dec x' x); subst; auto.
      apply IHelts.
      eapply PairSetFacts.add_3; eauto.
      congruence.
  Defined.
  
  Lemma in_mkPairs_in_set :
    forall x x' la s,
      PairSet.In (x, la) (mkPairs x' s)
      -> LaSet.In la s.
  Proof.
    intros x x' la s Hin.
    pose proof Hin as Hin'.
    apply mkPairs_keys_eq in Hin'; subst.
    apply in_elements_iff_in_laSet.
    unfold mkPairs in *.
    eapply in_mkPairs_in_set'; eauto.
  Defined.
  
  Lemma nt_in_pairs_in_elements :
    forall x la s ps,
      PairSet.In (x, la)
                 (fold_right
                    (fun (p : nonterminal * LaSet.t)
                         (acc : PairSet.t) =>
                       let (x, s) := p in
                       PairSet.union (mkPairs x s) acc) PairSet.empty
                    ps)
      -> InA (NtMap.eq_key (elt:=LaSet.t)) (x, s) ps.
  Proof.
    intros x la s ps Hin.
    induction ps as [| (x', s') ps]; simpl in *.
    - inv Hin.
    - apply PairSetFacts.union_1 in Hin.
      destruct Hin as [Hmk | Hfr].
      + apply InA_cons_hd.
        apply mkPairs_keys_eq in Hmk; subst. (* LTAC *)
        constructor.
      + apply InA_cons_tl; auto.
  Defined.
  
  Lemma In_InA_eq_key :
    forall x s s' ps,
      In (x, s) ps
      -> InA (NtMap.eq_key (elt := LaSet.t)) (x, s') ps.
  Proof.
    intros x s s' ps Hin.
    induction ps as [| (x', s'') ps]; simpl in *.
    - inv Hin.
    - destruct Hin as [Heq | Hin].
      + inv Heq.
        apply InA_cons_hd.
        constructor.
      + apply InA_cons_tl; auto.
  Defined.

  Lemma in_pairsOf_in_set' :
    forall x la s ps,
      PairSet.In (x, la)
                 (fold_right
                    (fun (p : nonterminal * LaSet.t) acc =>
                       let (x, s) := p in
                       PairSet.union (mkPairs x s) acc)
                    PairSet.empty
                    ps)
      -> In (x, s) ps
      -> NoDupA (NtMap.eq_key (elt := LaSet.t)) ps
      -> LaSet.In la s.
  Proof.
    intros x la s ps Hin Hin' Hnd.
    induction ps as [| (x', s') ps]; simpl in *.
    - inv Hin'.
    - destruct Hin' as [Heq | Hin'].
      + inv Heq.
        apply PairSetFacts.union_1 in Hin.
        destruct Hin as [Hmk | Hfr].
        * inv Hnd.
          eapply in_mkPairs_in_set; eauto.
        * exfalso.
          inv Hnd.
          eapply nt_in_pairs_in_elements in Hfr; eauto.
      + apply PairSetFacts.union_1 in Hin.
        destruct Hin as [Hmk | Hfr].
        * exfalso.
          inv Hnd.
          apply mkPairs_keys_eq in Hmk; subst.
          eapply In_InA_eq_key in Hin'; eauto.
        * inv Hnd.
          apply IHps; auto.
  Defined.        
  
  Lemma in_pairsOf_in_set :
    forall x la fi s,
      PairSet.In (x, la) (pairsOf fi)
      -> NtMap.find (elt:=LaSet.t) x fi = Some s
      -> LaSet.In la s.
  Proof.
    intros x la fi s Hin Hf.
    eapply in_pairsOf_in_set'; eauto.
    - apply find_in; auto.
    - apply NtMap.elements_3w.
  Defined.
  
  Lemma in_pairsOf_in_map_keys :
    forall x la fi,
      PairSet.In (x, la) (pairsOf fi)
      -> NtMap.In (elt:=LaSet.t) x fi.
  Proof.
    intros x la fi Hin.
    unfold pairsOf in *.
    apply NtMapFacts.elements_in_iff.
    induction (NtMap.elements fi) as [| (x', s) elts]; simpl in *.
    - inv Hin.
    - apply PairSetFacts.union_1 in Hin.
      destruct Hin as [Heq | Hin]; auto.
      + exists s.
        apply InA_cons_hd.
        apply mkPairs_keys_eq in Heq; subst.
        constructor; auto.
      + apply IHelts in Hin.
        destruct Hin as [s' Hin].
        exists s'.
        apply InA_cons_tl; auto.
  Defined.
  
  Lemma in_findOrEmpty_iff_in_pairsOf :
    forall x la fi,
      LaSet.In la (findOrEmpty x fi)
      <-> PairSet.In (x, la) (pairsOf fi).
  Proof.
    intros x la fi; split; intros Hin.
    - unfold findOrEmpty in *.
      destruct (NtMap.find x fi) as [s |] eqn:Hf.
      + eapply in_A_in_B_in_pairsOf; eauto.
        apply find_in; auto.
      + inv Hin.
    - unfold findOrEmpty in *.
      destruct (NtMap.find x fi) as [s |] eqn:Hf.
      + eapply in_pairsOf_in_set; eauto.
      + exfalso.
        eapply NtMapFacts.in_find_iff; eauto.
        eapply in_pairsOf_in_map_keys; eauto.
  Defined.
  
  Lemma not_in_findOrEmpty_not_in_pairsOf :
    forall x la fi,
      ~ LaSet.In la (findOrEmpty x fi)
      -> ~ PairSet.In (x, la) (pairsOf fi).
  Proof.
    intros x la fi Hnin.
    unfold not; intros Hin.
    apply Hnin; clear Hnin.
    unfold findOrEmpty in *.
    destruct (NtMap.find x fi) as [s |] eqn:Hf.
    - eapply in_pairsOf_in_set; eauto.
    - exfalso.
      apply NtMapFacts.not_find_in_iff in Hf.
      apply Hf; clear Hf.
      eapply in_pairsOf_in_map_keys; eauto.
  Defined.
  
  Lemma maps_equiv_sym :
    forall fi fi',
      NtMap.Equiv LaSet.Equal fi fi'
      -> NtMap.Equiv LaSet.Equal fi' fi.
  Proof.
    intros fi fi' Heq.
    unfold NtMap.Equiv in *.
    destruct Heq as [Hin Hmt].
    split.
    - intros x; split; intros Hin'; apply Hin; auto.
    - intros x s s' Hmt' Hmt''.
      apply Hmt with (e := s') in Hmt'; auto.
      LD.fsetdec.
  Defined.
  
  Lemma map_elements_InA_iff_In :
    forall x s fi,
      InA (NtMap.eq_key_elt (elt:=LaSet.t)) (x, s)
          (NtMap.elements (elt:=LaSet.t) fi)
      <-> In (x, s) (NtMap.elements (elt:=LaSet.t) fi).
  Proof.
    intros x s fi; split; intros Hin.
    - induction (NtMap.elements fi) as [| (x', s') elts]; simpl in *.
      + inv Hin.
      + apply InA_cons in Hin.
        destruct Hin as [Heq | Htl]; auto.
        inv Heq; simpl in *; subst; auto.
    - induction (NtMap.elements fi) as [| (x', s') elts]; simpl in *.
      + inv Hin.
      + destruct Hin as [Heq | Hin]; auto.
        inv Heq.
        apply InA_cons_hd.
        unfold NtMap.eq_key_elt; auto.
  Defined.
  
  Lemma kv_in_map_iff_in_elements :
    forall (x  : nonterminal)
           (s  : LaSet.t)
           (fi : first_map),
      NtMap.MapsTo x s fi
      <-> In (x, s) (NtMap.elements fi).
  Proof.
    intros x s fi; split; [intros Hmt | intros Hin].
    - apply map_elements_InA_iff_In. 
      rewrite <- NtMapFacts.elements_mapsto_iff; auto.
    - rewrite NtMapFacts.elements_mapsto_iff.
      apply map_elements_InA_iff_In; auto.
  Defined.
  
  Lemma in_elements_add :
    forall (x  : nonterminal)
           (s  : LaSet.t)
           (fi : first_map),
      In (x, s) (NtMap.elements (NtMap.add x s fi)).
  Proof.
    intros x s fi.
    apply kv_in_map_iff_in_elements.
    apply NtMap.add_1; auto.
  Defined.
  
  Lemma in_pairsOf_exists' :
    forall x la elts,
      PairSet.In (x, la)
                 (fold_right
                    (fun (p : nonterminal * LaSet.t) (acc : PairSet.t) =>
                       let (x, s) := p in
                       PairSet.union (mkPairs x s) acc) PairSet.empty elts)
      -> exists s : LaSet.t, In (x,s) elts /\ LaSet.In la s.
  Proof.
    intros x la elts Hin.
    induction elts as [| (x', s) elts]; simpl in *.
    - inv Hin.
    - apply PairSetFacts.union_1 in Hin.
      destruct Hin as [Heq | Hin]; auto.
      + pose proof Heq as Heq'. 
        apply mkPairs_keys_eq in Heq'; subst.
        apply in_mkPairs_in_set in Heq.
        exists s; split; auto.
      + apply IHelts in Hin.
        destruct Hin as [s' [Hin Hin']].
        exists s'; split; auto.
  Defined.

  Lemma in_pairsOf_exists :
    forall x la fi,
      PairSet.In (x, la) (pairsOf fi)
      -> exists s,
        NtMap.MapsTo x s fi
        /\ LaSet.In la s.
  Proof.
    intros x la fi Hin.
    apply in_pairsOf_exists' in Hin.
    destruct Hin as [s [Hin Hin']].
    exists s; split; auto.
    apply NtMapFacts.elements_mapsto_iff.
    apply map_elements_InA_iff_In; auto.
  Defined.
  
  Lemma find_values_eq :
    forall x (s s' : LaSet.t) fi,
      NtMap.find x (NtMap.add x s fi) = Some s'
      -> s = s'.
  Proof.
    intros x s s' fi Hf.
    pose proof NtMapFacts.add_eq_o as H.
    specialize (H LaSet.t fi x x s).
    assert (H' : x = x) by auto.
    apply H in H'.
    congruence.
  Defined.
  
  Lemma map_key_in_add :
    forall x s fi,
      NtMap.In (elt:=LaSet.t) x (NtMap.add x s fi).
  Proof.
    intros x s fi.
    apply NtMapFacts.add_in_iff.
    left; auto.
  Defined.
  
  Lemma in_add_keys_eq :
    forall x s la fi,
      LaSet.In la s
      -> PairSet.In (x, la) (pairsOf (NtMap.add x s fi)).
  Proof.
    intros x s la fi Hin.
    apply in_findOrEmpty_iff_in_pairsOf.
    unfold findOrEmpty.
    destruct (NtMap.find x (NtMap.add x s fi)) as [s' |] eqn:Hf.
    - apply find_values_eq in Hf; subst; auto.
    - exfalso.
      eapply NtMapFacts.in_find_iff; eauto.
      apply map_key_in_add.
  Defined.
  
  Lemma in_add_keys_neq :
    forall x y s la fi,
      x <> y
      -> PairSet.In (y, la) (pairsOf fi)
         <-> PairSet.In (y, la) (pairsOf (NtMap.add x s fi)).
  Proof.
    intros x y s la fi Hneq.
    split; intros Hin.
    - apply in_pairsOf_exists in Hin.
      destruct Hin as [s' [Hmt Hin]].
      eapply in_A_in_B_in_pairsOf; eauto.
      apply map_elements_InA_iff_In.
      rewrite <- NtMapFacts.elements_mapsto_iff.
      apply NtMap.add_2; auto.
    - apply in_pairsOf_exists in Hin.
      destruct Hin as [s' [Hmt Hin]].
      eapply NtMap.add_3 in Hmt; eauto.
      eapply in_A_in_B_in_pairsOf; eauto.
      apply map_elements_InA_iff_In.
      rewrite <- NtMapFacts.elements_mapsto_iff; auto.
  Defined.
  
  Lemma firstPass_equiv_or_exists' :
    forall nu ps suf pre fi,
      ps = pre ++ suf
      -> all_pairs_are_candidates fi ps
      -> NtMap.Equiv LaSet.Equal fi (firstPass suf nu fi)
         \/ exists x la,
          NtSet.In x (lhSet ps)
          /\ LaSet.In la (leftmostLookaheads ps)
          /\ ~ PairSet.In (x, la) (pairsOf fi)
          /\ PairSet.In (x, la) (pairsOf (firstPass suf nu fi)).
  Proof.
    intros nu ps suf.
    induction suf as [| (x, gamma) suf]; intros pre fi Happ Hap.
    - simpl in *. 
      left. (* LEMMA *)
      unfold NtMap.Equiv.
      split.
      + split; intros; auto.
      + intros k s s' Hmt Hmt'.
        apply NtMapFacts.find_mapsto_iff in Hmt.
        apply NtMapFacts.find_mapsto_iff in Hmt'.
        assert (s = s') by congruence; subst.
        apply LP.equal_refl.
    - simpl in *.
      destruct (IHsuf (pre ++ [(x, gamma)]) fi) as [Heq | Hex]; auto.
      + rewrite <- app_assoc.
        rewrite <- cons_app_singleton; auto.
      + match goal with 
        | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Hleq | Hnleq]
        end; auto.
        apply union_neq_exists_elt in Hnleq.
        destruct Hnleq as [la [Hnin Hin]].
        right.
        exists x; exists la.
        repeat split; auto.
        * rewrite Happ.
          apply in_lhSet_app.
        * eapply in_firstGamma_in_leftmost_lks with 
              (x := x)
              (nu := nu)
              (gamma := gamma); eauto.
          -- rewrite Happ.
             apply in_app_cons.
          -- eapply maps_equiv_in_firstGamma_iff; eauto.
        * apply not_in_findOrEmpty_not_in_pairsOf; auto.
          eapply maps_equiv_not_in_findOrEmpty; eauto.
          apply maps_equiv_sym; auto.
        * eapply in_A_in_B_in_pairsOf. (* need a better name for this lemma *)
          -- apply in_elements_add.
          -- LD.fsetdec.
      + match goal with 
        | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Hleq | Hnleq]
        end; auto.
        right.
        apply union_neq_exists_elt in Hnleq.
        destruct Hnleq as [la [Hnin Hin]].
        destruct Hex as [x' [la' [Hin' [Hin'' [Hnin' Hin''']]]]].
        repeat eexists; repeat split; eauto.
        destruct (NtSetFacts.eq_dec x' x); subst.
        * eapply in_A_in_B_in_pairsOf.
          -- apply in_elements_add.
          -- apply LaSetFacts.union_3.
             eapply in_pairsOf_in_set; eauto.
             unfold findOrEmpty.
             destruct (NtMap.find x (firstPass suf nu fi)) eqn:Hf; auto.
             ++ exfalso.
                apply in_pairsOf_in_map_keys in Hin'''.
                apply NtMapFacts.in_find_iff in Hin'''.
                congruence.
        * apply in_add_keys_neq; auto.
  Defined.

  Lemma in_pairsOf_in_value :
    forall x la s fi,
      PairSet.In (x, la) (pairsOf (NtMap.add x s fi))
      -> LaSet.In la s.
  Proof.
    intros x la s fi Hin.
    apply in_pairsOf_exists in Hin.
    destruct Hin as [s' [Hmt Hin]].
    apply NtMapFacts.add_mapsto_iff in Hmt. (* LEMMA, maybe *)
    destruct Hmt as [Heq | Hneq].
    - destruct Heq; subst; auto.
    - exfalso.
      destruct Hneq.
      congruence.
  Defined.

  Lemma firstPass_preserves_apac' :
    forall nu ps suf pre fi,
      ps = pre ++ suf
      -> all_pairs_are_candidates fi ps
      -> all_pairs_are_candidates (firstPass suf nu fi) ps.
  Proof.
    intros nu ps suf.
    induction suf as [| (x, gamma) suf]; intros pre fi Heq Hap.
    - simpl in *.
      auto.
    - simpl in *.
      match goal with
      | |- context[LaSet.eq_dec ?s1 ?s2] => destruct (LaSet.eq_dec s1 s2) as [Heq' | Hneq]
      end.
      + apply IHsuf with (pre := pre ++ [(x, gamma)]); auto.
        subst.
        rewrite <- app_assoc.
        auto.
      + apply IHsuf with (pre := pre ++ [(x, gamma)]) in Hap; clear IHsuf.
        * unfold all_pairs_are_candidates.
          intros x' la Hin.
          assert (Hinps : In (x, gamma) ps) by (subst; apply in_app_cons).
          destruct (NtSetFacts.eq_dec x' x); subst.
          -- split.
             ++ apply in_lhSet_app.
             ++ apply in_pairsOf_in_value in Hin.
                apply LaSetFacts.union_1 in Hin.
                destruct Hin as [Hfg | Hfe].
                ** eapply in_firstGamma_in_leftmost_lks; eauto.
                ** eapply Hap.
                   apply in_findOrEmpty_iff_in_pairsOf; eauto.
          -- apply in_add_keys_neq in Hin; auto.
        * subst; rewrite <- app_assoc; auto.
  Defined.                 
  
  Lemma firstPass_preserves_apac :
    forall nu ps fi,
      all_pairs_are_candidates fi ps
      -> all_pairs_are_candidates (firstPass ps nu fi) ps.
  Proof.
    intros.
    apply firstPass_preserves_apac' with (pre := []); auto.
  Defined.

  Lemma in_pairsOf_in_mkPairs :
    forall x la s fi,
      PairSet.In (x, la) (pairsOf (NtMap.add x s fi))
      <-> PairSet.In (x, la) (mkPairs x s).
  Proof.
    intros x la s fi; split; intros Hin.
    - apply in_set_in_mkPairs.
      eapply in_pairsOf_in_value; eauto.
    - eapply in_A_in_B_in_pairsOf.
      + apply in_elements_add.
      + eapply in_mkPairs_in_set; eauto.
  Defined.
  
  Lemma firstPass_subset : 
    forall nu ps fi,
      PairSet.Subset (pairsOf fi) (pairsOf (firstPass ps nu fi)).
  Proof.
    intros nu ps.
    induction ps as [| (x, gamma) ps]; intros fi; simpl in *.
    - PD.fsetdec.
    - match goal with
      | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Heq | Hneq]
      end; auto.
      eapply PairSetFacts.Subset_trans; eauto.
      intros (x', la) Hin.
      destruct (NtSetFacts.eq_dec x' x); subst.
      + apply in_add_keys_eq.
        apply LaSetFacts.union_3.
        apply in_findOrEmpty_iff_in_pairsOf; auto.
      + apply in_add_keys_neq; auto.
  Defined.
  
  Lemma firstPass_equiv_or_exists :
    forall nu ps fi,
      all_pairs_are_candidates fi ps
      -> NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
         \/ exists x la,
          NtSet.In x (lhSet ps)
          /\ LaSet.In la (leftmostLookaheads ps)
          /\ ~ PairSet.In (x, la) (pairsOf fi)
          /\ PairSet.In (x, la) (pairsOf (firstPass ps nu fi)).
  Proof.
    intros nu ps fi Hap.
    eapply firstPass_equiv_or_exists'; auto.
    rewrite app_nil_l; auto.
  Defined.
  
  Lemma firstPass_not_equiv_exists :
    forall nu ps fi,
      all_pairs_are_candidates fi ps
      -> ~ NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
      -> exists x la,
          NtSet.In x (lhSet ps)
          /\ LaSet.In la (leftmostLookaheads ps)
          /\ ~ PairSet.In (x, la) (pairsOf fi)
          /\ PairSet.In (x, la) (pairsOf (firstPass ps nu fi)).
  Proof.
    intros nu ps fi Hneq.
    destruct (firstPass_equiv_or_exists nu ps fi); auto; try congruence.
  Defined.
  
  Lemma firstPass_not_equiv_candidates_lt :
    forall nu ps fi,
      all_pairs_are_candidates fi ps
      -> ~ NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
      -> numFirstCandidates ps (firstPass ps nu fi) < numFirstCandidates ps fi.
  Proof.
    intros nu ps fi Hap Hneq.
    apply firstPass_not_equiv_exists in Hneq; auto.
    destruct Hneq as [x [la [Hin [Ht [Hnin Hin']]]]].
    apply PairSetEqProps.MP.subset_cardinal_lt with (x := (x, la)); try PD.fsetdec.
    - apply pairset_subset_subset_diffs.
      apply firstPass_subset.
    - apply ps_in_A_not_in_B_in_diff; auto.
      apply in_A_in_B_in_product; auto.
  Defined.
  
  Program Fixpoint mkFirstMap'
          (ps : list production)
          (nu : NtSet.t) 
          (fi : first_map)
          (pf : all_pairs_are_candidates fi ps)
          {measure (numFirstCandidates ps fi) } :=
    let fi' := firstPass ps nu fi in
    if first_map_equiv_dec fi fi' then
      fi
    else
      mkFirstMap' ps nu fi' (firstPass_preserves_apac nu ps fi pf).
  Next Obligation.
    apply firstPass_not_equiv_candidates_lt; auto.
  Defined.
  
  Definition empty_fi := NtMap.empty LaSet.t.
  
  Lemma empty_fi_apac :
    forall ps,
      all_pairs_are_candidates empty_fi ps.
  Proof.
    intros ps.
    unfold all_pairs_are_candidates; intros x la Hin.
    unfold pairsOf in *; simpl in *.
    inv Hin.
  Defined.
  
  Definition mkFirstMap (g : grammar) (nu : NtSet.t) :=
    let ps := prodsOf g in
    mkFirstMap' ps nu empty_fi (empty_fi_apac ps).
  
  (* Step 3 : compute the FOLLOW map for the grammar using the (correct) NULLABLE set and FIRST map. *)
  
  Fixpoint updateFo'
           (nu : NtSet.t)
           (fi : first_map)
           (lx  : nonterminal)
           (gamma : list symbol)
           (fo : follow_map) : follow_map :=
    match gamma with
    | [] => fo
    | T _ :: gamma' => updateFo' nu fi lx gamma' fo
    | NT rx :: gamma' =>
      let fo'   := updateFo' nu fi lx gamma' fo in
      let lSet  := findOrEmpty lx fo' in
      let rSet  := firstGamma gamma' nu fi in
      let additions := if nullableGamma gamma' nu then
                         LaSet.union lSet rSet
                       else
                         rSet
      in  match NtMap.find rx fo' with
          | Some rxFollow =>
            (* Only update FOLLOW(rx) if there's a new element to add *)
            if LaSet.subset additions rxFollow then
              fo'
            else
              let rxFollow' := LaSet.union rxFollow additions in
              NtMap.add rx rxFollow' fo'
          | None =>
            (* Only create a new FOLLOW(rx) if it contains at least one element *)
            if LaSet.is_empty additions then
              fo'
            else
              NtMap.add rx additions fo'
          end
    end.

  Definition updateFo (nu : NtSet.t)
                      (fi : first_map)
                      (p  : production)
                      (fo : follow_map) : follow_map :=
    let (x, gamma) := p in
    updateFo' nu fi x gamma fo.

  Definition followPass (ps : list production)
                        (nu : NtSet.t)
                        (fi : first_map)
                        (fo : follow_map) : follow_map :=
    fold_right (updateFo nu fi) fo ps.

  Definition follow_map_equiv_dec :
    forall m m' : first_map,
      {NtMap.Equiv LaSet.Equal m m'} + {~ NtMap.Equiv (LaSet.Equal) m m'}.
  Proof.
    apply first_map_equiv_dec.
  Defined.

  Fixpoint ntsOfGamma (gamma : list symbol) :=
    match gamma with
    | [] => NtSet.empty
    | T _ :: gamma' => ntsOfGamma gamma'
    | NT x :: gamma' => NtSet.add x (ntsOfGamma gamma')
    end.
  
  Definition ntsOfProd (p : production) : NtSet.t :=
    let (x, gamma) := p in
    NtSet.add x (ntsOfGamma gamma).
  
  Definition ntsOf (g : grammar) : NtSet.t :=
    fold_right (fun p acc => NtSet.union (ntsOfProd p) acc)
               (NtSet.singleton (start g))
               (prodsOf g).
  
  Fixpoint lookaheadsOfGamma (gamma : list symbol) : LaSet.t :=
    match gamma with
    | [] => LaSet.empty
    | T y :: gamma' => LaSet.add (LA y) (lookaheadsOfGamma gamma')
    | NT _ :: gamma' => lookaheadsOfGamma gamma'
    end.

  Definition lookaheadsOf (g : grammar) : LaSet.t :=
    fold_right (fun p acc =>
                  match p with
                  | (_, gamma) => LaSet.union (lookaheadsOfGamma gamma) acc
                  end)
               (LaSet.singleton EOF)
               (prodsOf g).
  
  Definition all_pairs_are_follow_candidates
             (fo : follow_map)
             (g  : grammar) : Prop :=
    forall x la,
      PairSet.In (x, la) (pairsOf fo)
      -> NtSet.In x (ntsOf g)
         /\ LaSet.In la (lookaheadsOf g).
  
  Definition numFollowCandidates
             (g : grammar)
             (fo : follow_map) : nat :=
    let allCandidates := product (ntsOf g) (lookaheadsOf g) in
    PairSet.cardinal (PairSet.diff allCandidates (pairsOf fo)).

  Lemma app_cons_apps :
    forall g x gpre sym gsuf,
      In (x, gpre ++ sym :: gsuf) (prodsOf g)
      -> In (x, (gpre ++ [sym]) ++ gsuf) (prodsOf g).
  Proof.
    intros; rewrite <- app_assoc; auto.
  Defined.
  
  Lemma find_in_pairsOf :
    forall x la s fo,
      NtMap.find x fo = Some s
      -> LaSet.In la s
      -> PairSet.In (x, la) (pairsOf fo).
  Proof.
    intros x la s fo Hf Hin.
    apply in_findOrEmpty_iff_in_pairsOf.
    unfold findOrEmpty.
    rewrite Hf; auto.
  Defined.
  
  Lemma medial_nt_in_ntsOfGamma :
    forall x gpre gsuf,
      NtSet.In x (ntsOfGamma (gpre ++ NT x :: gsuf)).
  Proof.
    intros x gpre gsuf.
    induction gpre as [| sym gpre]; simpl in *; auto.
    - ND.fsetdec.
    - destruct sym as [y | x']; auto.
      ND.fsetdec.
  Defined.

  Lemma medial_nt_in_ntsOf :
    forall g lx rx gpre gsuf,
      In (lx, gpre ++ NT rx :: gsuf) (prodsOf g)
      -> NtSet.In rx (ntsOf g).
  Proof.
    intros g lx rx gpre gsuf Hin.
    unfold ntsOf; unfold prodsOf in *.
    induction g.(prods) as [| (lx', gamma) ps]; simpl in *.
    - inv Hin.
    - destruct Hin as [Heq | Hin].
      + inv Heq.
        apply NtSetFacts.union_2.
        apply NtSetFacts.add_2.
        apply medial_nt_in_ntsOfGamma.
      + apply NtSetFacts.union_3; auto.
  Defined.
  
  Lemma in_findOrEmpty_exists_set :
    forall x la m,
      LaSet.In la (findOrEmpty x m)
      -> exists s,
        NtMap.find x m = Some s
        /\ LaSet.In la s.
  Proof.
    intros x la m Hin.
    unfold findOrEmpty in *.
    destruct (NtMap.find x m) as [s |]; eauto.
    inv Hin.
  Defined.

  Lemma medial_t_in_lookaheadsOfGamma :
    forall y gpre gsuf,
      LaSet.In (LA y) (lookaheadsOfGamma (gpre ++ T y :: gsuf)).
  Proof.
    intros y gpre gsuf.
    induction gpre as [| sym gpre]; simpl in *.
    - LD.fsetdec.
    - destruct sym as [y' | x]; auto.
      LD.fsetdec.
  Defined.
  
  Lemma medial_t_in_lookaheadsOf :
    forall g x gpre gsuf y,
      In (x, gpre ++ T y :: gsuf) (prodsOf g)
      -> LaSet.In (LA y) (lookaheadsOf g).
  Proof.
    intros g x gpre gsuf y Hin.
    unfold lookaheadsOf; unfold prodsOf in *.
    induction g.(prods) as [| [(x', gamma) f] ps]; simpl in *.
    - inv Hin.
    - destruct Hin as [Heq | Hin].
      + inv Heq.
        apply LaSetFacts.union_2.
        apply medial_t_in_lookaheadsOfGamma.
      + apply LaSetFacts.union_3; auto.
  Defined.
  
  Lemma first_sym_in_lookaheadsOf :
    forall g la sym,
      first_sym g la sym
      -> forall x,
        sym = NT x
        -> LaSet.In la (lookaheadsOf g).
  Proof.
    intros g la sym Hfs.
    induction Hfs; intros x' Heq.
    - inv Heq.
    - inv Heq.
      destruct s as [y | x].
      + inv Hfs.
        eapply medial_t_in_lookaheadsOf; eauto.
        eapply in_xprods_in_prodsOf; eauto.
      + eapply IHHfs; eauto.
  Defined.
  
  Lemma first_map_la_in_lookaheadsOf :
    forall g x s la fi,
      first_map_for fi g
      -> NtMap.find x fi = Some s
      -> LaSet.In la s
      -> LaSet.In la (lookaheadsOf g).
  Proof.
    intros g x s la fi Hfm Hf Hin.
    eapply first_sym_in_lookaheadsOf; eauto.
    eapply Hfm; eauto.
  Defined.
  
  Lemma in_firstGamma_in_lookaheadsOf :
    forall g nu fi x gsuf gpre la,
      first_map_for fi g
      -> In (x, gpre ++ gsuf) (prodsOf g)
      -> LaSet.In la (firstGamma gsuf nu fi)
      -> LaSet.In la (lookaheadsOf g).
  Proof.
    intros g nu fi x gsuf.
    induction gsuf as [| sym gsuf]; intros gpre la Hfm Hin Hin'; simpl in *.
    - inv Hin'.
    - destruct nullableSym.
      + apply LaSetFacts.union_1 in Hin'.
        destruct Hin' as [Hfs | Hfg].
        * destruct sym as [y | x']; simpl in *.
          -- apply LaSetFacts.singleton_1 in Hfs; subst.
             eapply medial_t_in_lookaheadsOf; eauto.
          -- apply in_findOrEmpty_exists_set in Hfs.
             destruct Hfs as [s [Hf Hin']].
             eapply first_map_la_in_lookaheadsOf; eauto.
        * apply IHgsuf with (gpre := gpre ++ [sym]); auto.
          apply app_cons_apps; auto.
      + (* lemma *)
        destruct sym as [y | x']; simpl in *.
        * apply LaSetFacts.singleton_1 in Hin'; subst.
          eapply medial_t_in_lookaheadsOf; eauto.
        * apply in_findOrEmpty_exists_set in Hin'.
          destruct Hin' as [s [Hf Hin']].
          eapply first_map_la_in_lookaheadsOf; eauto.
  Defined.

  Lemma updateFo_preserves_apac :
    forall g nu fi lx gsuf gpre fo,
      first_map_for fi g
      -> In (lx, gpre ++ gsuf) (prodsOf g)
      -> all_pairs_are_follow_candidates fo g
      -> all_pairs_are_follow_candidates (updateFo' nu fi lx gsuf fo) g.
  Proof.
    intros g nu fi lx gsuf.
    induction gsuf as [| sym gsuf]; intros gpre fo Hfm Hin Hap; simpl in *; auto.
    pose proof Hap as Hap'.
    apply IHgsuf with (gpre := gpre ++ [sym]) in Hap; try (apply app_cons_apps; auto); clear IHgsuf; auto.
    destruct sym as [y | rx]; auto.
    destruct (NtMap.find rx (updateFo' nu fi lx gsuf fo)) as [rxFollow |] eqn:Hf.
    - match goal with
      | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end; auto.
      unfold all_pairs_are_follow_candidates.
      intros x la Hin'.
      destruct (NtSetFacts.eq_dec x rx); subst.
      + apply in_pairsOf_in_value in Hin'.
        apply LaSetFacts.union_1 in Hin'.
        destruct Hin' as [Hfo | Hu].
        * split.
          -- eapply medial_nt_in_ntsOf; eauto.
          -- eapply find_in_pairsOf in Hf; eauto.
             apply Hap in Hf.
             destruct Hf; auto.
        * destruct (nullableGamma gsuf nu) eqn:Hng.
          -- apply LaSetFacts.union_1 in Hu.
             destruct Hu as [Hfe | Hfg].
             ++ split.
                ** eapply medial_nt_in_ntsOf; eauto.
                ** apply in_findOrEmpty_iff_in_pairsOf in Hfe.
                   apply Hap in Hfe.
                   destruct Hfe; auto.
             ++ split.
                ** eapply medial_nt_in_ntsOf; eauto.
                ** eapply in_firstGamma_in_lookaheadsOf with
                       (gpre := gpre ++ [NT rx]); eauto.
                   apply app_cons_apps; eauto.
          -- split.
             ++ eapply medial_nt_in_ntsOf; eauto.
             ++ eapply in_firstGamma_in_lookaheadsOf with
                    (gpre := gpre ++ [NT rx]); eauto.
                apply app_cons_apps; eauto.
      + apply Hap.
        apply in_add_keys_neq in Hin'; auto.
    - match goal with
      | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
      end; auto.
      unfold all_pairs_are_follow_candidates.
      intros x la Hin'.
      destruct (NtSetFacts.eq_dec x rx); subst.
      + apply in_pairsOf_in_value in Hin'.
        destruct (nullableGamma gsuf nu) eqn:Hng.
        * apply LaSetFacts.union_1 in Hin'.
          destruct Hin' as [Hfe | Hfg].
          -- split.
             ++ eapply medial_nt_in_ntsOf; eauto.
             ++ unfold all_pairs_are_follow_candidates in Hap.
                apply in_findOrEmpty_iff_in_pairsOf in Hfe.
                apply Hap in Hfe.
                destruct Hfe; auto.
          -- split.
             ++ eapply medial_nt_in_ntsOf; eauto.
             ++ eapply in_firstGamma_in_lookaheadsOf with
                    (gpre := gpre ++ [NT rx]); eauto.
                apply app_cons_apps; eauto.
        * split.
          -- eapply medial_nt_in_ntsOf; eauto.
          -- eapply in_firstGamma_in_lookaheadsOf with
                 (gpre := gpre ++ [NT rx]); eauto.
             apply app_cons_apps; eauto.
      + apply Hap.
        apply in_add_keys_neq in Hin'; auto.
  Defined.
    
  Lemma followPass_preserves_apac' :
    forall g nu fi suf pre fo,
      first_map_for fi g
      -> pre ++ suf = (prodsOf g)
      -> all_pairs_are_follow_candidates fo g
      -> all_pairs_are_follow_candidates (followPass suf nu fi fo) g.
  Proof.
    intros g nu fi suf.
    induction suf as [| (x, gamma) suf]; intros pre fo Hfm Happ Hap; simpl in *; auto.
    pose proof Happ as Happ'.
    rewrite cons_app_singleton in Happ.
    rewrite app_assoc in Happ.
    eapply IHsuf in Hap; eauto.
    apply updateFo_preserves_apac with (gpre := nil); simpl in *; auto.
    rewrite <- Happ'.
    apply in_app_cons.
  Defined.
  
  Lemma followPass_preserves_apac :
    forall g nu fi fo,
      first_map_for fi g
      -> all_pairs_are_follow_candidates fo g
      -> all_pairs_are_follow_candidates (followPass (prodsOf g) nu fi fo) g.
  Proof.
    intros.
    eapply followPass_preserves_apac'; eauto.
    rewrite app_nil_l; auto.
  Defined.

  Lemma updateFo_subset :
    forall nu fi fo x x' la gamma,
      PairSet.In (x, la) (pairsOf fo)
      -> PairSet.In (x, la) (pairsOf (updateFo' nu fi x' gamma fo)).
  Proof.
    intros nu fi fo x x' la gamma Hin.
    induction gamma as [| sym gamma]; simpl in *; auto.
    destruct sym as [y | rx]; auto.
    destruct (NtMap.find rx (updateFo' nu fi x' gamma fo)) as [rxFollow |] eqn:Hf.
    - match goal with
      | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
      end; auto.
      destruct (NtSetFacts.eq_dec x rx); subst.
      + apply in_add_keys_eq.
        apply LaSetFacts.union_2.
        (* to do : rename fi to something generic in this lemma *)
        eapply in_pairsOf_in_set with
            (fi := updateFo' nu fi x' gamma fo); eauto.
      + apply in_add_keys_neq; auto.
    - match goal with
      | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
      end; auto.
      destruct (NtSetFacts.eq_dec x rx); subst.
      + exfalso.
        apply in_pairsOf_in_map_keys in IHgamma.
        apply NtMapFacts.in_find_iff in IHgamma.
        congruence.
      + apply in_add_keys_neq; auto.    
  Defined.
  
  Lemma followPass_subset :
    forall nu fi fo ps,
      PairSet.Subset (pairsOf fo) (pairsOf (followPass ps nu fi fo)).
  Proof.
    intros nu fi fo ps.
    induction ps as [| (x, gamma) ps]; simpl in *; auto.
    - PD.fsetdec.
    - eapply PairSetFacts.Subset_trans; eauto.
      unfold PairSet.Subset.
      intros (x', la) Hin.
      eapply updateFo_subset; eauto.
  Defined.
  
  Lemma subset_false_not_Subset :
    forall a b,
      LaSet.subset a b = false
      -> ~ LaSet.Subset a b.
  Proof.
    intros a b Hs.
    unfold not; intros HS.
    apply LaSetFacts.subset_iff in HS; congruence.
  Defined.
  
  Lemma not_Subset_exists_elt :
    forall a b,
      ~ LaSet.Subset a b
      -> exists la,
        LaSet.In la a
        /\ ~ LaSet.In la b.
  Proof.
    intros a b Hns.
    unfold LaSet.Subset in Hns.
    apply union_neq_exists_elt.
    unfold not; intros.
    apply Hns.
    intros la Hin.
    LD.fsetdec.
  Defined.
  
  Lemma la_in_fo_in_lookaheadsOf :
    forall g x fo xFollow la,
      NtMap.find x fo = Some xFollow
      -> LaSet.In la xFollow
      -> all_pairs_are_follow_candidates fo g
      -> LaSet.In la (lookaheadsOf g).
  Proof.
    intros g x fo xFollow la Hf Hin Hap.
    eapply Hap.
    eapply find_in_pairsOf; eauto.
  Defined.
  
  Lemma not_empty_exists_elt :
    forall s,
      LaSet.is_empty s = false
      -> exists la,
        LaSet.In la s.
  Proof.
    intros s Hie.
    apply LaSetEqProps.choose_mem_3 in Hie.
    destruct Hie as [la [_ Hmem]].
    exists la.
    rewrite <- LaSet.mem_spec; auto.
  Defined.

  Lemma updateFo_equiv_or_exists' :
    forall g nu fi lx gsuf gpre fo,
      first_map_for fi g
      -> In (lx, gpre ++ gsuf) (prodsOf g)
      -> all_pairs_are_follow_candidates fo g
      -> NtMap.Equiv LaSet.Equal fo (updateFo' nu fi lx gsuf fo)
         \/ exists (x' : NtSet.elt) (la : LaSet.elt),
          NtSet.In x' (ntsOf g) /\
          LaSet.In la (lookaheadsOf g) /\
          ~ PairSet.In (x', la) (pairsOf fo) /\
          PairSet.In (x', la) (pairsOf (updateFo' nu fi lx gsuf fo)).
  Proof.
    intros g nu fi lx gsuf.
    induction gsuf as [| sym gsuf]; intros gpre fo Hfm Hin Hap; simpl in *.
    - left.
      (* LEMMA *)
      unfold NtMap.Equiv.
      split.
      + split; intros; auto.
      + intros k s s' Hmt Hmt'.
        apply NtMapFacts.find_mapsto_iff in Hmt.
        apply NtMapFacts.find_mapsto_iff in Hmt'.
        assert (s = s') by congruence; subst.
        apply LP.equal_refl.
    - pose proof Hin as Hin'.
      rewrite cons_app_singleton in Hin.
      rewrite app_assoc in Hin.
      pose proof Hin as Hin''.
      eapply IHgsuf in Hin; clear IHgsuf; eauto.
      destruct sym as [y | rx]; auto.
      destruct (NtMap.find rx (updateFo' nu fi lx gsuf fo)) as [rxFollow |] eqn:Hf.
      + match goal with
        | |- context[LaSet.subset ?s1 ?s2] => destruct (LaSet.subset s1 s2) eqn:Hsub
        end; auto.
        right.
        apply subset_false_not_Subset in Hsub.
        apply not_Subset_exists_elt in Hsub.
        destruct Hsub as [la [H_la_in H_la_nin]].
        exists rx; exists la; repeat split; auto.
        * eapply medial_nt_in_ntsOf; eauto.
        * destruct (nullableGamma gsuf nu) eqn:Hng.
          -- apply LaSetFacts.union_1 in H_la_in.
             destruct H_la_in as [Hfe | Hfg].
             ++ eapply updateFo_preserves_apac with
                    (nu := nu)
                    (gpre := gpre ++ [NT rx]) in Hap; eauto.
                apply in_findOrEmpty_exists_set in Hfe.
                destruct Hfe as [lxFollow [Hf_lx Hin_lx]].
                eapply la_in_fo_in_lookaheadsOf; eauto.
             ++ eapply in_firstGamma_in_lookaheadsOf; eauto.
          -- eapply in_firstGamma_in_lookaheadsOf; eauto.
        * unfold not; intros Hp.
          apply H_la_nin.
          eapply updateFo_subset in Hp.
          eapply in_pairsOf_in_set; eauto.
        * apply in_add_keys_eq.
          apply LaSetFacts.union_3; auto.
      + match goal with
        | |- context[LaSet.is_empty ?s] => destruct (LaSet.is_empty s) eqn:Hemp
        end; auto.
        right.
        apply not_empty_exists_elt in Hemp.
        destruct Hemp as [la H_la_in].
        exists rx; exists la; repeat split; auto.
        * eapply medial_nt_in_ntsOf; eauto.
        * destruct (nullableGamma gsuf nu) eqn:Hng.
          -- apply LaSetFacts.union_1 in H_la_in.
             destruct H_la_in as [Hfe | Hfg].
             ++ eapply updateFo_preserves_apac with
                    (nu := nu)
                    (gpre := gpre ++ [NT rx]) in Hap; eauto.
                apply in_findOrEmpty_exists_set in Hfe.
                destruct Hfe as [lxFollow [Hf_lx Hin_lx]].
                eapply la_in_fo_in_lookaheadsOf; eauto.
             ++ eapply in_firstGamma_in_lookaheadsOf; eauto.
          -- eapply in_firstGamma_in_lookaheadsOf; eauto.
        * unfold not; intros Hp.
          eapply updateFo_subset with
              (nu := nu)
              (fi := fi)
              (x' := lx)
              (gamma := gsuf) in Hp.
          apply in_pairsOf_exists in Hp.
          destruct Hp as [rxFollow [Hmt H_in_rxFollow]].
          apply NtMapFacts.find_mapsto_iff in Hmt.
          congruence.
        * apply in_add_keys_eq; auto.
  Defined.

  Lemma updateFo_equiv_or_exists :
    forall g nu fi x gamma fo,
      first_map_for fi g
      -> In (x, gamma) (prodsOf g)
      -> all_pairs_are_follow_candidates fo g
      -> NtMap.Equiv LaSet.Equal fo (updateFo' nu fi x gamma fo)
         \/ exists (x' : NtSet.elt) (la : LaSet.elt),
          NtSet.In x' (ntsOf g) /\
          LaSet.In la (lookaheadsOf g) /\
          ~ PairSet.In (x', la) (pairsOf fo) /\
          PairSet.In (x', la) (pairsOf (updateFo' nu fi x gamma fo)).
  Proof.
    intros.
    eapply updateFo_equiv_or_exists'; eauto.
    rewrite app_nil_l; auto.
  Defined.
  
  Lemma mapsto_in :
    forall k (v : LaSet.t) m,
      NtMap.MapsTo k v m
      -> NtMap.In k m.
  Proof.
    intros.
    rewrite NtMapFacts.find_mapsto_iff in H.
    eapply ntmap_find_in; eauto.
  Defined.
  
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
  Defined.
  
  Lemma ntmap_equiv_trans :
    forall m1 m2 m3,
      NtMap.Equiv LaSet.Equal m1 m2
      -> NtMap.Equiv LaSet.Equal m2 m3
      -> NtMap.Equiv LaSet.Equal m1 m3.
  Proof.
    intros m1 m2 m3 H12 H23.
    unfold NtMap.Equiv.
    split; [intros k; split; intros Hin | intros k s1 s3 Hmt1 Hmt3].
    - apply H23; apply H12; auto.
    - apply H12; apply H23; auto.
    - pose proof Hmt1 as Hmt1'.
      apply mapsto_in in Hmt1.
      apply H12 in Hmt1.
      apply k_in_map_exists_v in Hmt1.
      destruct Hmt1 as [s2 Hmt2].
      eapply LP.equal_trans.
      + eapply H12; eauto.
      + eapply H23; eauto.   
  Defined.
  
  Lemma followPass_equiv_or_exists' :
    forall g nu fi suf pre fo,
      first_map_for fi g
      -> all_pairs_are_follow_candidates fo g
      -> pre ++ suf = (prodsOf g)
      -> NtMap.Equiv LaSet.Equal fo (followPass suf nu fi fo)
         \/ exists x la,
          NtSet.In x (ntsOf g)
          /\ LaSet.In la (lookaheadsOf g)
          /\ ~ PairSet.In (x, la) (pairsOf fo)
          /\ PairSet.In (x, la) (pairsOf (followPass suf nu fi fo)).
  Proof.
    intros g nu fi suf.
    induction suf as [| (x, gamma) suf]; intros pre fo Hfm Hap Happ; simpl in *.
    - left. (* LEMMA *)
      unfold NtMap.Equiv.
      split.
      + split; intros; auto.
      + intros k s s' Hmt Hmt'.
        apply NtMapFacts.find_mapsto_iff in Hmt.
        apply NtMapFacts.find_mapsto_iff in Hmt'.
        assert (s = s') by congruence; subst.
        apply LP.equal_refl.
    - destruct (IHsuf (pre ++ [(x, gamma)]) fo) as [Heq | Hex]; clear IHsuf; auto.
      + rewrite <- app_assoc; auto.
      + pose proof updateFo_equiv_or_exists.
        specialize (H g nu fi x gamma (followPass suf nu fi fo)).
        eapply followPass_preserves_apac' with
            (suf := suf) in Hap; eauto.
        * apply H in Hap; auto.
          destruct Hap; auto.
          -- left.
             eapply ntmap_equiv_trans; eauto.
          -- destruct H0 as [x' [la [Hin [Hin' [Hnin Hin'']]]]].
             right.
             exists x'; exists la; repeat split; auto.
             unfold not; intros.
             apply Hnin.
             apply followPass_subset; auto.
          -- rewrite <- Happ.
             apply in_app_cons.
        * rewrite cons_app_singleton in Happ.
          rewrite app_assoc in Happ; eauto.
      + destruct Hex as [x' [la [Hin [Hin' [Hnin Hin'']]]]].
        right.
        exists x'; exists la; repeat split; auto.
        apply updateFo_subset; auto.
  Defined.
  
  Lemma followPass_equiv_or_exists :
    forall g nu fi fo,
      first_map_for fi g
      -> all_pairs_are_follow_candidates fo g
      -> NtMap.Equiv LaSet.Equal fo (followPass (prodsOf g) nu fi fo)
         \/ exists x la,
          NtSet.In x (ntsOf g)
          /\ LaSet.In la (lookaheadsOf g)
          /\ ~ PairSet.In (x, la) (pairsOf fo)
          /\ PairSet.In (x, la) (pairsOf (followPass (prodsOf g) nu fi fo)).
  Proof.
    intros.
    eapply followPass_equiv_or_exists'; eauto.
    rewrite app_nil_l; auto.
  Defined.
  
  Lemma followPass_not_equiv_exists :
    forall g nu fi fo,
      first_map_for fi g
      -> all_pairs_are_follow_candidates fo g
      -> ~ NtMap.Equiv LaSet.Equal fo (followPass (prodsOf g) nu fi fo)
      -> exists x la,
          NtSet.In x (ntsOf g)
          /\ LaSet.In la (lookaheadsOf g)
          /\ ~ PairSet.In (x, la) (pairsOf fo)
          /\ PairSet.In (x, la) (pairsOf (followPass (prodsOf g) nu fi fo)).
  Proof.
    intros g nu fi fo Hap Hneq.
    destruct (followPass_equiv_or_exists g nu fi fo); auto; try congruence.
  Defined.
  
  Lemma followPass_not_equiv_candidates_lt :
    forall g nu fi fo,
      first_map_for fi g
      -> all_pairs_are_follow_candidates fo g
      -> ~ NtMap.Equiv LaSet.Equal fo (followPass (prodsOf g) nu fi fo)
      -> numFollowCandidates g (followPass (prodsOf g) nu fi fo) < numFollowCandidates g fo.
  Proof.
    intros g nu fi fo Hfm Hap Hneq.
    apply followPass_not_equiv_exists in Hneq; auto.
    destruct Hneq as [x [la [Hx [Hla [Hps Hps']]]]].
    apply PP.subset_cardinal_lt with (x := (x, la)).
    - apply pairset_subset_subset_diffs.
      apply followPass_subset.
    - apply ps_in_A_not_in_B_in_diff; auto.
      apply in_A_in_B_in_product; auto.
    - PD.fsetdec.
  Defined.
  
  Program Fixpoint mkFollowMap'
          (g  : grammar)
          (nu : NtSet.t) 
          (fi : first_map)
          (fi_pf : first_map_for fi g)
          (fo : follow_map)
          (apac_pf : all_pairs_are_follow_candidates fo g)
          {measure (numFollowCandidates g fo) } :=
    let fo' := followPass (prodsOf g) nu fi fo in
    if follow_map_equiv_dec fo fo' then
      fo
    else
      mkFollowMap' g nu fi fi_pf fo' (followPass_preserves_apac g nu fi fo fi_pf apac_pf).
  Next Obligation.
    apply followPass_not_equiv_candidates_lt; auto.
  Defined.
  
  Definition initial_fo g :=
    NtMap.add (start g) (LaSet.singleton EOF) (NtMap.empty LaSet.t).
  
  Lemma start_in_ntsOf :
    forall g,
      NtSet.In (start g) (ntsOf g).
  Proof.
    intros g.
    unfold ntsOf; unfold prodsOf.
    induction g.(prods) as [| (x, gamma) ps]; simpl in *; ND.fsetdec.
  Defined.
  
  Lemma EOF_in_lookaheadsOf :
    forall g,
      LaSet.In EOF (lookaheadsOf g).
  Proof.
    intros g.
    unfold lookaheadsOf; unfold prodsOf.
    induction g.(prods) as [| [(x, gamma) f] ps]; simpl in *; LD.fsetdec.
  Defined.
  
  Lemma initial_fo_apac :
    forall g,
      all_pairs_are_follow_candidates (initial_fo g) g.
  Proof.
    intros g.
    unfold all_pairs_are_follow_candidates.
    intros x la Hin.
    unfold initial_fo in *.
    destruct (NtSetFacts.eq_dec x (start g)); subst.
    - apply in_pairsOf_in_value in Hin.
      apply LaSetFacts.singleton_1 in Hin; subst.
      split.
      + apply start_in_ntsOf. 
      + apply EOF_in_lookaheadsOf. 
    - apply in_add_keys_neq in Hin; auto.
      inv Hin.
  Defined.
  
  Definition mkFollowMap
             (g : grammar)
             (nu : NtSet.t)
             (fi : first_map)
             (fi_pf : first_map_for fi g) : follow_map :=
    mkFollowMap' g nu fi fi_pf (initial_fo g) (initial_fo_apac g).
 
  (* Step 4 : build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

  Definition table_entry := (xprod * lookahead)%type.
  
  Definition fromLookaheadList (xp  : xprod) (las : list lookahead) :
    list table_entry :=
    List.map (fun la => (xp, la)) las.
  
  (* To do: rename this function, or create a single version *)
  Fixpoint firstGamma' (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :
    list lookahead :=
    match gamma with 
    | [] => []
    | T y :: _ => [LA y]
    | NT x :: gamma' => 
      let xFirst := match NtMap.find x fi with
                    | Some s => LaSet.elements s
                    | None => []
                    end
      in  if NtSet.mem x nu then xFirst ++ firstGamma' gamma' nu fi else xFirst
    end.
  
  Definition firstEntries (xp : xprod) (nu : NtSet.t) (fi : first_map) :
    list table_entry :=
    fromLookaheadList xp (firstGamma' (rhs xp) nu fi).
  
  Definition followLookahead (x : nonterminal) (gamma : list symbol)
             (nu : NtSet.t) (fo : follow_map) : list lookahead := 
    if nullableGamma gamma nu then
      match NtMap.find x fo with 
      | Some s => LaSet.elements s
      | None => []
      end
    else 
      [].
  
  Definition followEntries (xp : xprod) (nu : NtSet.t) (fo : follow_map) :
    list table_entry :=
    fromLookaheadList xp (followLookahead (lhs xp) (rhs xp) nu fo).
  
  Definition entriesForProd nu fi fo xp : list table_entry :=
    firstEntries xp nu fi ++ followEntries xp nu fo.
  
  Definition mkEntries' nu fi fo xps : list table_entry :=
    flat_map (entriesForProd nu fi fo) xps.
  
  Definition mkEntries nu fi fo g : list table_entry :=
    mkEntries' nu fi fo g.(prods).

  (* Step 5 : build a parse table from a (correct) list of parse table entries *)

  Definition ambigMessage
             (la : lookahead)
             (x : nonterminal)
             (gamma gamma' : list symbol) : string :=
    "The grammar is not LL(1); " ++ show_lookahead la ++ " is a lookahead token
     for the following two productions with the same left-hand side and
     different right-hand sides:\n\n"
     ++ show_prod (x, gamma)
     ++ "\n"
     ++ show_prod (x, gamma').
  
  Definition empty_table := ParseTable.empty xprod.

  Definition addEntry (e : table_entry) (s : Datatypes.sum string parse_table) :
    Datatypes.sum string parse_table :=
    match s with
    | inl msg => inl msg
    | inr tbl =>
      let (xp, la) := e in
      match xp with
      | existT _ (x, gamma) _ =>
        match pt_lookup x la tbl with
        | None => inr (pt_add x la xp tbl)
        (* the cell already contains an entry *)
        | Some (existT _ (x', gamma') _) =>
          if production_eq_dec (x, gamma) (x', gamma') then
            inr tbl
          else
            inl (ambigMessage la x gamma gamma')
        end
      end
    end.
  
  Definition mkParseTable (ps : list table_entry) :
    Datatypes.sum string parse_table :=
    fold_right addEntry (inr empty_table) ps.

  (* Create the message that the generator returns in the case of a grammar
     with duplicate productions. *)
  Definition dupMessage (p : production) : string :=
    "The following production appears multiple times in the grammar:\n\n"
    ++ (show_prod p)
    ++ "\n\nThe grammar is either ambiguous (if the production appears with 
        different actions), or redundant (if it appears multiple times with
        the same action).".
  
End GeneratorFn.

