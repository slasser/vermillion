Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.

Definition prod_la_pair := (production * LaSet.t)%type.
Definition prod_la_pair_wf (g : grammar) (p : prod_la_pair) :=
  match p with
  | ((x, gamma), laSet) => lookahead_set_for laSet x gamma g
  end.
Definition prod_la_pairs_wf (ps : list prod_la_pair) (g : grammar) :=
  Forall (prod_la_pair_wf g) ps.

Definition empty_pt := NtMap.empty (LaMap.t (list symbol)).

Definition singletonLaMap la gamma :=
  LaMap.add la gamma (LaMap.empty (list symbol)).
  
Definition addEntry (x : nonterminal) (la : lookahead) (gamma : list symbol) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl => 
    match NtMap.find x tbl with
    | None => Some (NtMap.add x (singletonLaMap la gamma) tbl)
    | Some m =>
      match LaMap.find la m with
      | None => Some (NtMap.add x (LaMap.add la gamma m) tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None
      end
    end
  end.

Definition addEntries (p : prod_la_pair) (o : option parse_table) :=
  match p with
  | ((x, gamma), laSet) =>
    fold_right (fun la o => addEntry x la gamma o) o (LaSet.elements laSet)
  end.

Definition mkParseTable (productions_with_la_sets : list prod_la_pair) :=
  fold_right addEntries (Some empty_pt) productions_with_la_sets.

Definition tbl_sound_wrt_pairs tbl ps :=
  forall x gamma la,
    pt_lookup x la tbl = Some gamma
    -> exists laSet,
      In ((x, gamma), laSet) ps /\ LaSet.In la laSet.

Definition tbl_complete_wrt_pairs tbl ps :=
  forall x gamma la laSet,
    In ((x, gamma), laSet) ps
    -> LaSet.In la laSet
    -> pt_lookup x la tbl = Some gamma.

Definition tbl_correct_wrt_pairs tbl ps :=
  tbl_sound_wrt_pairs tbl ps /\ tbl_complete_wrt_pairs tbl ps.

Lemma invariant_iff_parse_table_for :
  forall g ps tbl,
    g.(productions) = map fst ps
    -> prod_la_pairs_wf ps g
    -> tbl_correct_wrt_pairs tbl ps
       <-> parse_table_for tbl g.
Proof.
  intros g ps tbl Heq Hwf.
  split.
  - intros Hinv.
    destruct Hinv as [Hts Htc].
    unfold parse_table_for.
    split.
    + unfold pt_sound.
      intros x la gamma Hlk.
      unfold tbl_sound_wrt_pairs in Hts.
      apply Hts in Hlk.
      destruct Hlk as [laSet [Hpin Hlin]].
      unfold prod_la_pairs_wf in Hwf.
      rewrite Forall_forall in Hwf.
      apply Hwf in Hpin.
      unfold prod_la_pair_wf in Hpin.
      unfold lookahead_set_for in Hpin.
      destruct Hpin; auto.
    + unfold pt_complete.
      intros la x gamma Hlk.
      pose proof Hlk as Hlk'.
      unfold lookahead_for in Hlk.
      destruct Hlk as [Hin Hlk].
      pose proof in_map_iff.
      specialize H with (y := (x, gamma)) (f := fst) (l := ps).
      rewrite <- Heq in H.
      apply H in Hin.
      destruct Hin as [pr [Hfst Hin]].
      destruct pr as (prod, laSet).
      destruct prod as (y, gamma').
      inv Hfst.
      unfold tbl_complete_wrt_pairs in Htc.
      eapply Htc; eauto.
      unfold prod_la_pairs_wf in Hwf.
      rewrite Forall_forall in Hwf.
      apply Hwf in Hin.
      inv Hin.
      apply H1; auto.
  - intros Hpt.
    unfold tbl_correct_wrt_pairs.
    destruct Hpt as [Hsou Hcom].
    split.
    + unfold tbl_sound_wrt_pairs.
      intros x gamma la Hlk.
      pose proof Hlk as Hlk'.
      unfold pt_sound in Hsou.
      apply Hsou in Hlk.
      unfold prod_la_pairs_wf in Hwf.
      rewrite Forall_forall in Hwf.
      destruct Hlk as [Hin Hlk].
      pose proof in_map_iff.
      specialize H with (y := (x, gamma)) (f := fst) (l := ps).
      rewrite <- Heq in H.
      apply H in Hin.
      destruct Hin as [pr [Hfst Hin]].
      destruct pr as (prod, laSet).
      destruct prod as (y, gamma').
      inv Hfst.
      pose proof Hin as Hin'.
      apply Hwf in Hin.
      unfold prod_la_pair_wf in Hin.
      unfold lookahead_set_for in Hin.
      destruct Hin as [Hls Hlc].
      exists laSet; split; auto.
    + unfold tbl_complete_wrt_pairs.
      intros x gamma la laSet Hin Hla.
      unfold pt_complete in Hcom.
      apply Hcom.
      unfold prod_la_pairs_wf in Hwf.
      rewrite Forall_forall in Hwf.
      apply Hwf in Hin.
      unfold prod_la_pair_wf in Hin.
      destruct Hin.
      apply H; auto.
Qed.

Lemma addEntry_None_eq_None :
  forall x la gamma,
    addEntry x la gamma None = None.
Proof.
  auto.
Qed.

Lemma addEntries_None_eq_None :
  forall p,
    addEntries p None = None.
Proof.
  intros p.
  destruct p as ((x, gamma), laSet); simpl.
  induction (LaSet.elements laSet); simpl; auto.
  rewrite IHl.
  apply addEntry_None_eq_None.
Qed.

Lemma addEntries_preserves_Some :
  forall p ps tbl,
    addEntries p (mkParseTable ps) = Some tbl
    -> exists tbl',
      mkParseTable ps = Some tbl'.
Proof.
  intros.
  destruct (mkParseTable ps) as [tbl' |].
  + exists tbl'; auto.
  + rewrite addEntries_None_eq_None in H; inv H.
Qed.

Lemma addEntries_preserves_invariant :
  forall tbl' tbl p ps,
    tbl_correct_wrt_pairs tbl' ps
    -> addEntries p (Some tbl') = Some tbl
    -> tbl_correct_wrt_pairs tbl (p :: ps).
Proof.
Admitted.

Lemma mkParseTable_satisfies_invariant :
  forall ps g tbl,
    prod_la_pairs_wf ps g
    -> mkParseTable ps = Some tbl
    -> tbl_correct_wrt_pairs tbl ps.
Proof.
  intros ps. 
  induction ps as [| p ps]; intros g tbl Hwf Hmk; simpl in *.
  - inv Hmk.
    unfold tbl_correct_wrt_pairs.
    split.
    + unfold tbl_sound_wrt_pairs.
      intros x gamma la Hlk.
      unfold pt_lookup in Hlk.
      destruct (NtMap.find x empty_pt) eqn:Hnf.
      * rewrite NtMapFacts.empty_o in Hnf; inv Hnf.
      * inv Hlk.
    + unfold tbl_complete_wrt_pairs.
      intros x gamma la laSet Hin; inv Hin.
  - pose proof Hmk as Hmk'.
    apply addEntries_preserves_Some in Hmk.
    destruct Hmk as [tbl' Hmk].
    rewrite Hmk in Hmk'.
    inv Hwf.
    eapply addEntries_preserves_invariant; eauto.
Qed.

Lemma mkParseTable_sound :
  forall ps g tbl,
    g.(productions) = map fst ps
    -> prod_la_pairs_wf ps g
    -> mkParseTable ps = Some tbl
    -> parse_table_for tbl g.
Proof.
  intros ps g tbl Hfst Hwf Hmk.
  eapply invariant_iff_parse_table_for; eauto.
  eapply mkParseTable_satisfies_invariant; eauto.
Qed.
  
Lemma mkParseTable_correct : 
  forall (ps : list prod_la_pair)
         (tbl : parse_table)
         (g : grammar),
    prod_la_pairs_wf g ps
    -> mkParseTable ps = Some tbl
       <-> parse_table_for tbl g.
Proof.
  intros ps tbl g Hwf.
  split.
  - (* prove mkParseTable sound -- if it returns parse table tbl,
 tbl is a parse table for g *)
    intros Hmk.
    apply tbl_correct_for_pl_pairs_parse_table_for with
        (ps := ps).
    

(*
Lemma mkParseTable_correct : 
  forall (productions_and_la_sets : list (production * LaSet.t))
         (tbl : parse_table),
    -> mkParseTable productions_and_la_sets = Some tbl
    -> forall (start : nonterminal)
              (productions : list production),
        productions = map fst productions_and_la_sets
        (* productions_and_la_sets is well-formed *)
        -> 
       <-> parse_table_for tbl g.
Proof.
  intros; split.
  - revert g tbl H.
    induction productions_and_la_sets.
    + (* empty list of productions and lookahead sets --
         the grammar's productions must be empty, so mkParseTable should return 
         an empty table *)
      intros g tbl Hprods Hmk.
      simpl in *.
      inv Hmk.
      unfold parse_table_for; split.
      * unfold pt_minimal; intros x la gamma laMap Hnf Hlf.
        exfalso; eapply NtMapFacts.empty_in_iff.
        apply ntmap_find_in in Hnf; eauto.
      * unfold pt_complete; intros x la gamma Hlf.
        exfalso.
        unfold lookahead_for in Hlf.
        destruct Hlf as [Hin _].
        rewrite Hprods in Hin; inv Hin.
    + intros g tbl Hprods Hmk.
      destruct a as [[x gamma] laSet].
*)