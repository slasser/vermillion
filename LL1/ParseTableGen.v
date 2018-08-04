Require Import List.
Require Import Nat Ndec NArith.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.Lemmas.
Require Import LL1.ParseTable.

Import ListNotations.

Definition prod_la_pair := (production * lookahead)%type.

Definition empty_pt := ParseTable.empty (list symbol).

Definition addEntry (p : prod_la_pair) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | ((x, gamma), la) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition mkParseTable (ps : list prod_la_pair) :=
  fold_right addEntry (Some empty_pt) ps.

Definition pairs_wf ps g :=
  forall x gamma la,
    In ((x, gamma), la) ps <-> lookahead_for la x gamma g.

Definition tbl_correct_wrt_pairs tbl ps :=
  forall x gamma la,
    pt_lookup x la tbl = Some gamma <-> In ((x, gamma), la) ps.

Lemma invariant_iff_parse_table_for :
  forall g ps tbl,
    pairs_wf ps g
    -> tbl_correct_wrt_pairs tbl ps
       <-> parse_table_for tbl g.
Proof.
  intros g ps tbl Hwf.
  split.
  - intros Htc.
    unfold tbl_correct_wrt_pairs in Htc.
    split.
    + unfold pt_sound.
      intros x la gamma Hlk.
      apply Hwf.
      apply Htc; auto.
    + unfold pt_complete.
      intros la x gamma Hlk.
      apply Htc.
      apply Hwf; auto.
  - intros Hpt.
    destruct Hpt as [Hsou Hcom].
    unfold tbl_correct_wrt_pairs.
    intros x gamma la.
    split.
    + intros Hlk.
      apply Hwf.
      apply Hsou; auto.
    + intros Hin.
      apply Hcom.
      apply Hwf; auto.
Qed.

Lemma addEntry_preserves_Some :
  forall p o tbl,
    addEntry p o = Some tbl
    -> exists tbl',
      o = Some tbl'.
Proof.
  intros p o tbl Hadd.
  destruct p as ((x, gamma), la).
  destruct o as [tbl' |] eqn:Ho.
  - exists tbl'; auto.
  - unfold addEntry in Hadd; inv Hadd.
Qed.

Lemma duplicate_preserves_invariant :
  forall tbl ps x la gamma,
    tbl_correct_wrt_pairs tbl ps
    -> pt_lookup x la tbl = Some gamma
    -> tbl_correct_wrt_pairs tbl (((x, gamma), la) :: ps).
Proof.
  intros tbl ps x la gamma Htc Hlk.
  unfold tbl_correct_wrt_pairs.
  intros x' gamma' la'.
  split.
  - intros Hlk'.
    unfold tbl_correct_wrt_pairs in Htc.
    apply Htc in Hlk'.
    right; auto.
  - intros Hin.
    inv Hin.
    + inv H; auto.
    + apply Htc; auto.
Qed.

Lemma lookup_add_or :
  forall x x' la la' gamma gamma' tbl,
    pt_lookup x' la' (pt_add x la gamma tbl) = Some gamma'
    -> (x = x' /\ la = la' /\ gamma = gamma')
       \/ pt_lookup x' la' tbl = Some gamma'.
Proof.
  intros x x' la la' gamma gamma' tbl Hlk.
  unfold pt_lookup in Hlk; unfold pt_add in Hlk.
  rewrite ParseTableFacts.add_o in Hlk.
  destruct (ParseTableFacts.eq_dec (x, la) (x', la')).
  - inv e.
    inv Hlk.
    left; auto.
  - right; auto.
Qed.

Lemma new_entry_preserves_invariant :
  forall tbl ps x la gamma,
    tbl_correct_wrt_pairs tbl ps
    -> pt_lookup x la tbl = None
    -> tbl_correct_wrt_pairs (pt_add x la gamma tbl) (((x, gamma), la) :: ps).
Proof.
  intros tbl ps x la gamma Htc Hlk.
  unfold tbl_correct_wrt_pairs.
  intros x' gamma' la'.
  split.
  - intros Hlk'.
    apply lookup_add_or in Hlk'.
    inv Hlk'.
    + destruct H as [Hx [Hla Hgamma]]; subst.
      left; auto.
    + apply Htc in H.
      right; auto.
  - intros Hin.
    inv Hin.
    + inv H.
      unfold pt_lookup.
      unfold pt_add.
      apply ParseTableFacts.add_eq_o; auto.
    + apply Htc in H.
      destruct (ParseTableFacts.eq_dec (x, la) (x', la')). 
      * inv e; congruence.
      * unfold pt_lookup.
        unfold pt_add.
        rewrite ParseTableFacts.add_neq_o; auto.
Qed.

Lemma addEntry_preserves_invariant :
  forall p ps tbl' tbl,
    tbl_correct_wrt_pairs tbl' ps
    -> addEntry p (Some tbl') = Some tbl
    -> tbl_correct_wrt_pairs tbl (p :: ps).
Proof.
  intros ((x, gamma), la) ps tbl' tbl Htc Hadd.
  unfold addEntry in Hadd.
  destruct (pt_lookup x la tbl') as [gamma' |] eqn:Hlk.
  - destruct (list_eq_dec symbol_eq_dec gamma gamma').
    + inv e.
      inv Hadd.
      apply duplicate_preserves_invariant; auto.
    + inv Hadd.
  - inv Hadd.
    apply new_entry_preserves_invariant; auto.
Qed.

Lemma empty_table_correct_wrt_empty_pairs :
  tbl_correct_wrt_pairs empty_pt [].
Proof.
  unfold tbl_correct_wrt_pairs.
  intros x gamma la.
  split.
  - intros Hlk.
    unfold pt_lookup in Hlk.
    rewrite ParseTableFacts.empty_o in Hlk; inv Hlk.
  - intros Hin; inv Hin.
Qed.

Lemma mkParseTable_sound_wrt_invariant :
  forall ps tbl,
    mkParseTable ps = Some tbl
    -> tbl_correct_wrt_pairs tbl ps.
Proof.
  intros ps.
  induction ps as [| p ps]; intros tbl Hmk; simpl in *.
  - inv Hmk.
    apply empty_table_correct_wrt_empty_pairs.
  - pose proof Hmk as Hmk'.
    apply addEntry_preserves_Some in Hmk.
    destruct Hmk as [tbl' Hmk].
    rewrite Hmk in Hmk'.
    eapply addEntry_preserves_invariant; eauto.
Qed.

Lemma mkParseTable_sound :
  forall ps g tbl,
    pairs_wf ps g
    -> mkParseTable ps = Some tbl
    -> parse_table_for tbl g.
Proof.
  intros ps g tbl Hwf Hmk.
  eapply invariant_iff_parse_table_for; eauto.
  eapply mkParseTable_sound_wrt_invariant; eauto.
Qed.      

