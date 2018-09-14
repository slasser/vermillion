Require Import List.
Require Import MSets.
Require Import Program.Wf.

Require Import Lib.Grammar.
Require Import Lib.Tactics.
Require Import Lib.Utils.

Require Import LL1.ParseTable.

Import ListNotations.
Import MSetDecide.

Module Import NSD := WDecideOn NT_as_DT NtSet.

(* Step 1: compute the NULLABLE set for a grammar *)

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

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
  fsetdec.
Qed.

Lemma nullablePass_subset :
  forall ps nu,
    NtSet.Subset nu (nullablePass ps nu).
Proof.
  induction ps as [| p ps]; intros nu; simpl in *; try fsetdec.
  unfold updateNu.
  destruct p as (x, gamma).
  destruct (nullableGamma gamma (nullablePass ps nu)); auto.
  apply NtSetEqProps.MP.subset_add_2; auto.
Qed.

Lemma In_lhSet_cons :
  forall x' ps x gamma,
    NtSet.In x' (lhSet ps)
    -> NtSet.In x' (lhSet ((x, gamma) :: ps)).
Proof.
  intros.
  unfold lhSet in *; simpl in *; fsetdec.
Qed.

Lemma nullablePass_eq_or_exists :
  forall ps nu,
    NtSet.Equal nu (nullablePass ps nu)
    \/ exists x,
      NtSet.In x (lhSet ps)
      /\ ~NtSet.In x nu
      /\ NtSet.In x (nullablePass ps nu).
Proof.
  induction ps as [| (x, gamma) ps]; intros nu; simpl in *; try fsetdec.
  destruct (nullableGamma gamma (nullablePass ps nu)).
  - destruct (NtSetEqProps.MP.In_dec x nu).
    + destruct (IHps nu).
      * left; fsetdec.
      * destruct H as [x' [Hin [Hnin Hin']]].
        right; eexists; repeat split; eauto.
        -- apply In_lhSet_cons; auto.
        -- fsetdec.
    + right; eexists; repeat split; eauto; try fsetdec.
      unfold lhSet; simpl; fsetdec.
  - destruct (IHps nu); auto.
    destruct H as [x' [Hin [Hnin Hin']]].
    right; eexists; split; eauto.
    apply In_lhSet_cons; auto.
Qed.

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
Qed.

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
  apply NtSetEqProps.MP.subset_cardinal_lt with (x := x); try fsetdec.
  apply subset_subset_diffs.
  apply nullablePass_subset.
Qed.
  
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
  mkNullableSet' g.(productions) NtSet.empty.

(* Step 2 : compute the FIRST map for the grammar using the (correct) NULLABLE set. *)

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
Fixpoint firstGamma (gamma : list symbol) (nu : nullable_set) (fi : first_map) :=
  match gamma with
  | [] => LaSet.empty
  | sym :: gamma' =>
    if nullableSym sym nu then
      LaSet.union (firstSym sym fi) (firstGamma gamma' nu fi)
    else firstSym sym fi
    end.

Definition updateFi (nu : nullable_set) (p : production) (fi : first_map) : first_map :=
  let (x, gamma) := p in
  let fg := firstGamma gamma nu fi in
  let xFirst := findOrEmpty x fi in
  let xFirst' := LaSet.union fg xFirst in
  if LaSet.eq_dec xFirst xFirst' then (* necessary? *)
    fi
  else
    NtMap.add x xFirst' fi.

Definition firstPass (ps : list production) (nu : nullable_set) (fi : first_map) : first_map :=
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
Qed.
  
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
Module Import PairSetDecide := WDecideOn Pair_as_DT PairSet.

Definition mkPairs (x : nonterminal) (laSet : LaSet.t) :=
  LaSet.fold (fun la acc => PairSet.add (x, la) acc) laSet PairSet.empty.

(*
Definition pairsOf (fi : first_map) : PairSet.t :=
  NtMap.fold (fun x laSet acc => PairSet.union (mkPairs x laSet) acc) fi PairSet.empty. 
*)

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

(* To do : there must be a way to avoid duplicating this *)
Lemma pairset_subset_subset_diffs :
  forall a b c : PairSet.t,
    PairSet.Subset a b 
    -> PairSet.Subset (PairSet.diff c b) (PairSet.diff c a).
Proof.
  fsetdec.
Qed.

Lemma firstPass_subset : 
  forall nu ps fi,
    PairSet.Subset (pairsOf fi) (pairsOf (firstPass ps nu fi)).
Proof.
Admitted.

Lemma in_A_not_in_B_in_diff :
  forall elt a b,
    PairSet.In elt a
    -> ~ PairSet.In elt b
    -> PairSet.In elt (PairSet.diff a b).
Proof.
  fsetdec.
Qed.

Module MP := MSetProperties.Properties NtSet.
 
Module LSP := MSetProperties.Properties LaSet.
Module LSD := WDecideOn Lookahead_as_DT LaSet.

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
Qed.

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
Qed.

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
  - destruct Hin; subst; try fsetdec.
    apply IHlas in H; fsetdec.
Qed.

Lemma in_set_in_mkPairs :
  forall (x  : nonterminal)
         (la : lookahead)
         (s  : LaSet.t),
    LaSet.In la s
    -> PairSet.In (x, la) (mkPairs x s).
Proof.
  intros x la s Hin.
  unfold mkPairs.
  rewrite LSP.fold_spec_right.
  apply in_set_in_mkPairs'. 
  rewrite <- in_rev.
  apply in_elements_iff_in_laSet; auto.
Qed.

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
      fsetdec.
    + eapply IHxs in H; eauto.
      fsetdec.
Qed.

(* To do : add module name before all fsetdec uses *)
Lemma in_A_in_B_in_product :
  forall x la ntSet laSet,
    NtSet.In x ntSet
    -> LaSet.In la laSet
    -> PairSet.In (x, la) (product ntSet laSet).
Proof.
  intros x la ntSet laSet Hin Hin'.
  unfold product.
  rewrite MP.fold_spec_right.
  apply in_A_in_B_in_product'; auto.
  rewrite <- in_rev.
  apply in_elements_iff_in_ntSet; auto.
Qed.

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
    destruct (leftmostLookahead gamma') as [la'' |]; auto; LSD.fsetdec.
Qed.

Lemma firstPass_equiv_or_exists :
  forall nu ps fi,
    NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
    \/ exists x la,
      NtSet.In x (lhSet ps)
      /\ LaSet.In la (leftmostLookaheads ps)
      /\ ~ PairSet.In (x, la) (pairsOf fi)
      /\ PairSet.In (x, la) (pairsOf (firstPass ps nu fi)).
Proof.
Admitted.
(*
  intros nu ps.
  induction ps as [| (x, gamma) ps]; intros fi.
  - simpl in *. 
    left. (* LEMMA *)
    unfold NtMap.Equiv.
    split.
    + split; intros; auto.
    + intros k s s' Hmt Hmt'.
      apply NtMapFacts.find_mapsto_iff in Hmt.
      apply NtMapFacts.find_mapsto_iff in Hmt'.
      assert (s = s') by congruence; subst.
      apply LSP.equal_refl.
  - simpl in *.
    match goal with 
    | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Heq | Hneq]
    end.
    + destruct (IHps fi); auto.
      destruct H as [x' [la [Hin [Hin' [Hnin Hin'']]]]].
      right.
      exists x'; exists la.
      repeat split; auto.
      * apply In_lhSet_cons; auto.
      * apply in_leftmostLookaheads_cons; auto.
    + assert (exists la, 
                 ~ LaSet.In la (findOrEmpty x (firstPass ps nu fi))
                 /\ LaSet.In la (firstGamma gamma nu (firstPass ps nu fi))) by admit.
      destruct H as [la [Hnin Hin]].
      destruct (IHps fi).
      * right.
        exists x; exists la.
        repeat split; auto.
        -- unfold lhSet; simpl. 
           NSD.fsetdec.
        -- unfold leftmostLookaheads; simpl.
           destruct (leftmostLookahead gamma) as [la' |].
           ++ destruct (lookahead_eq_dec la' la); subst.
              ** LSD.fsetdec.
              ** apply LaSetFacts.add_neq_iff; auto.
                 

      * destruct H as [x' [la' [Hin' [Hin'' [Hnin' Hin''']]]]].
        right.
        exists x'; exists la'.
        repeat split; auto.
        -- apply In_lhSet_cons; auto.
        -- apply in_leftmostLookaheads_cons; auto.
        -- admit.
      right.
      exists x; exists la.
      repeat split; auto.
      * unfold lhSet; simpl. 
        NSD.fsetdec.
      * unfold leftmostLookaheads; simpl.
        destruct (leftmostLookahead gamma).
        -- LSD.fsetdec.
*)

Lemma firstPass_not_equiv_exists :
  forall nu ps fi,
    ~ NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
    -> exists x la,
      NtSet.In x (lhSet ps)
      /\ LaSet.In la (leftmostLookaheads ps)
      /\ ~ PairSet.In (x, la) (pairsOf fi)
      /\ PairSet.In (x, la) (pairsOf (firstPass ps nu fi)).
Proof.
  intros nu ps fi Hneq.
  destruct (firstPass_equiv_or_exists nu ps fi); try congruence.
Qed.
  
Lemma firstPass_not_equiv_candidates_lt :
  forall nu ps fi,
    ~ NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
    -> numFirstCandidates ps (firstPass ps nu fi) < numFirstCandidates ps fi.
Proof.
  intros nu ps fi Hneq.
  apply firstPass_not_equiv_exists in Hneq.
  destruct Hneq as [x [la [Hin [Ht [Hnin Hin']]]]].
  apply PairSetEqProps.MP.subset_cardinal_lt with (x := (x, la)); try fsetdec.
  - apply pairset_subset_subset_diffs.
    apply firstPass_subset.
  - apply in_A_not_in_B_in_diff; auto.
    apply in_A_in_B_in_product; auto.
Qed.

Definition all_pairs_are_candidates (fi : first_map) (ps : list production) :=
  forall x la,
    PairSet.In (x, la) (pairsOf fi)
    -> NtSet.In x (lhSet ps)
       /\ LaSet.In la (leftmostLookaheads ps).

Lemma cons_app_singleton :
  forall A (x : A) (ys : list A),
    x :: ys = [x] ++ ys.
Proof.
  auto.
Qed.

Lemma firstPass_preserves_apac' :
  forall nu ps suf pre fi,
    ps = pre ++ suf
    -> all_pairs_are_candidates fi ps
    -> all_pairs_are_candidates (firstPass suf nu fi) ps.
Proof.
Admitted.

Lemma firstPass_preserves_apac :
  forall nu ps fi,
    all_pairs_are_candidates fi ps
    -> all_pairs_are_candidates (firstPass ps nu fi) ps.
Proof.
  intros.
  apply firstPass_preserves_apac' with (pre := []); auto.
Qed.

(*
Lemma in_leftmostLookaheads_exists :
  forall la ps,
    exists x gpre y
Hin : In (x, gpre ++ T y :: gsuf) ps
  Hapac : all_pairs_are_candidates fi ps
  Hfa : Forall (fun sym : symbol => isNT sym = true) gpre
  ============================
  LaSet.In (LA y) (leftmostLookaheads ps)
*)

Definition all_nt(gamma : list symbol) :=
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
Qed.

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
      LSD.fsetdec.
    + apply IHps in H.
      apply in_leftmostLookaheads_cons; auto.
Qed.

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
Qed.

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
Qed.

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
Qed.

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
Qed.

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
Qed.
      

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
      apply LSP.equal_refl.
  - simpl in *.
    rewrite cons_app_singleton in Happ.
    rewrite app_assoc in Happ.
    destruct (IHsuf (pre ++ [(x,gamma)]) fi Happ Hap) as [Heq | Hex].
    + (* folding over ps hasn't changed fi *) 
      match goal with 
      | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Hleq | Hnleq]
      end; auto.
      assert (exists la, 
                 ~ LaSet.In la (findOrEmpty x (firstPass suf nu fi))
                 /\ LaSet.In la (firstGamma gamma nu (firstPass suf nu fi))) by admit.
      destruct H as [la [Hnin Hin]].
      right.
      exists x; exists la.
      repeat split; auto.
      * admit.
      * eapply in_firstGamma_in_leftmost_lks with 
            (x := x)
            (nu := nu)
            (gamma := gamma); eauto.
        -- admit.
        -- admit.
      * admit.
      * admit.
    + match goal with 
      | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s') as [Hleq | Hnleq]
      end; auto.
      destruct Hex as [x' [la [Hin [Hin' [Hnin Hin'']]]]].
      right.
      exists x'; exists la.
      repeat split; auto.
      admit.
  
Admitted.

(*
Lemma foo' :
  forall fi ps,
    first_map_wf fi ps
    -> LaSet.In la (firstGamma gamma nu fi)
    -> LaSet.In la (leftmostLookaheads ps)
Happ : first_map_wf (firstPass suf nu fi) ps
  Hfm : first_map_wf fi ps
  n : ~
      LaSet.eq (findOrEmpty x (firstPass suf nu fi))
        (LaSet.union (firstGamma gamma nu (firstPass suf nu fi))
           (findOrEmpty x (firstPass suf nu fi)))
  la : lookahead
  Hin : PairSet.In (x, la)
          (pairsOf
             (NtMap.add x
                (LaSet.union (firstGamma gamma nu (firstPass suf nu fi))
                   (findOrEmpty x (firstPass suf nu fi))) 
                (firstPass suf nu fi)))
  H : LaSet.In la (firstGamma gamma nu (firstPass suf nu fi))
  ============================
  LaSet.In la (leftmostLookaheads ps)
*)

Lemma in_app_cons :
  forall A (x : A) (pre suf : list A),
    In x (pre ++ x :: suf).
Proof.
  intros A x pre suf.
  induction pre; simpl; auto.
Qed.

(*
Lemma foo :
  forall nu ps suf pre fi,
    ps = pre ++ suf
    -> first_map_wf fi ps
    -> first_map_wf (firstPass suf nu fi) ps.
Proof.
  intros nu ps suf.
  induction suf as [| (x, gamma) suf]; intros pre fi Happ Hfm.
  - auto.
  - assert (Hin : In (x, gamma) ps) by (rewrite Happ; apply in_app_cons).
    rewrite cons_app_singleton in Happ.
    rewrite app_assoc in Happ.
    apply IHsuf with (fi := fi) in Happ; clear IHsuf; auto.
    simpl.
    match goal with
    | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s')
    end; auto.
    unfold first_map_wf.
    intros x' la Hin'.
    destruct (NtSetFacts.eq_dec x' x) as [Heq | Hneq]; subst.
    + assert (LaSet.In la (LaSet.union (firstGamma gamma nu (firstPass suf nu fi))
                                       (findOrEmpty x (firstPass suf nu fi)))) by admit.
      apply LaSetFacts.union_1 in H.
      destruct H.
      * admit.
      * unfold findOrEmpty in H.
        destruct (NtMap.find x (firstPass suf nu fi)) eqn:Hf.
        -- apply Happ with (x := x). 
           admit.
        -- inv H.
    + assert (PairSet.In (x', la) (pairsOf (firstPass suf nu fi))) by admit.
      eapply Happ; eauto.
    

re
  - auto.
  - simpl in *.
    match goal with
    | |- context[LaSet.eq_dec ?s ?s'] => destruct (LaSet.eq_dec s s')
    end.
    + unfold first_map_wf.
      intros x' la Hin.
      unfold leftmostLookaheads; simpl.
      destruct (leftmostLookahead gamma) as [la' |].
      * destruct (lookahead_eq_dec la' la); subst; try LSD.fsetdec.
        apply LaSetFacts.add_neq_iff; auto.
        assert (first_map_wf fi ps) by admit.
        apply IHps in H.
        unfold first_map_wf in H.
        eapply H; eauto.
      * assert (first_map_wf fi ps) by admit.
        apply IHps in H.
        eapply H; eauto.
    + unfold first_map_wf.
      intros x' la Hin.
      destruct (NtSetFacts.eq_dec x' x); subst.
      * assert (LaSet.In la (LaSet.union (firstGamma gamma nu (firstPass ps nu fi)) (findOrEmpty x (firstPass ps nu fi)))) by admit.
        apply LaSetFacts.union_1 in H.
        destruct H.
        -- 
  
Admitted.
*)

Program Fixpoint mkFirstSet'
        (ps : list production)
        (nu : nullable_set) 
        (fi : first_map)
        (pf : all_pairs_are_candidates fi ps)
        {measure (numFirstCandidates ps fi) } :=
  let fi' := firstPass ps nu fi in
  if first_map_equiv_dec fi fi' then
    fi
  else
    mkFirstSet' ps nu fi' (firstPass_preserves_apac nu ps fi pf).
Next Obligation.
  apply firstPass_not_equiv_candidates_lt; auto.
Defined.

(* Step 4 : build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition table_entry := (nonterminal * lookahead * list symbol)%type.

Lemma table_entry_dec :
  forall e e2 : table_entry,
    {e = e2} + {e <> e2}.
Proof.
  repeat decide equality.
Defined.

Definition fromLookaheadList x gamma las : list table_entry :=
  map (fun la => (x, la, gamma)) las.

Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :
  list lookahead :=
  match gamma with 
  | [] => []
  | T y :: _ => [LA y]
  | NT x :: gamma' => 
    let xFirst := match NtMap.find x fi with
                  | Some s => LaSet.elements s
                  | None => []
                  end
    in  if NtSet.mem x nu then xFirst ++ firstGamma gamma' nu fi else xFirst
  end.

Definition firstEntries x gamma nu fi :=
  fromLookaheadList x gamma (firstGamma gamma nu fi).

Definition followLookahead x gamma nu fo :=
  if nullableGamma gamma nu then
    match NtMap.find x fo with 
    | Some s => LaSet.elements s
    | None => []
    end
  else 
    [].

Definition followEntries x gamma nu fo :=
  fromLookaheadList x gamma (followLookahead x gamma nu fo).

Definition entriesForProd nu fi fo (prod : production) : list table_entry :=
  let (x, gamma) := prod in
  firstEntries x gamma nu fi ++ followEntries x gamma nu fo.

Definition mkEntries' nu fi fo ps :=
  flat_map (entriesForProd nu fi fo) ps.

Definition mkEntries nu fi fo g :=
  mkEntries' nu fi fo g.(productions).

(* Step 5 : build a parse table from a (correct) list of parse table entries *)

Definition empty_table := ParseTable.empty (list symbol).

Definition addEntry (p : table_entry) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | (x, la, gamma) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition mkParseTable (ps : list table_entry) : option parse_table :=
  fold_right addEntry (Some empty_table) ps.

(* Combining all of the steps into a single function *)
(* The type of this function will change as I add code for computing NULLABLE, etc. *)

Definition genTableForGrammar g fi fo :=
  let nu := mkNullableSet g in
  let es := mkEntries nu fi fo g in
  mkParseTable es.

