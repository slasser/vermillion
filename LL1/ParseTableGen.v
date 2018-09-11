Require Import List.
Require Import MSets.
Require Import Program.Wf.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.
Import MSetDecide.

Module Import NtSetDecide := WDecideOn NT_as_DT NtSet.

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
  induction ps as [| p ps]; intros nu; simpl in *; try fsetdec.
  unfold updateNu.
  destruct p as (x, gamma).
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

Definition pairsOf (fi : first_map) : PairSet.t :=
  NtMap.fold (fun x laSet acc => PairSet.union (mkPairs x laSet) acc) fi PairSet.empty. 

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
  NtSet.fold (fun x acc => PairSet.union (mkPairs x l) acc) n PairSet.empty.

Definition numFirstCandidates (ps : list production) (fi : first_map) :=
  let allCandidates := product (lhSet ps) (leftmostLookaheads ps) in
  PairSet.cardinal (PairSet.diff allCandidates (pairsOf fi)).

Lemma firstPass_not_equiv_exists :
  forall nu ps fi,
    ~ NtMap.Equiv LaSet.Equal fi (firstPass ps nu fi)
    -> exists x la,
      NtSet.In x (lhSet ps)
      /\ LaSet.In la (leftmostLookaheads ps)
      /\ ~ PairSet.In (x, la) (pairsOf fi)
      /\ PairSet.In (x, la) (pairsOf (firstPass ps nu fi)).
Proof.
Admitted.

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

Lemma in_A_in_B_in_product :
  forall x la ntSet laSet,
    NtSet.In x ntSet
    -> LaSet.In la laSet
    -> PairSet.In (x, la) (product ntSet laSet).
Proof.
Admitted.

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

Program Fixpoint mkFirstSet'
        (ps : list production)
        (nu : nullable_set) 
        (fi : first_map)
        {measure (numFirstCandidates ps fi) } :=
  let fi' := firstPass ps nu fi in
  if first_map_equiv_dec fi fi' then
    fi
  else
    mkFirstSet' ps nu fi'.
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

