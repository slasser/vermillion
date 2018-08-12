Require Import List.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Definition pt_entries_correct ps g :=
  forall x la gamma,
    In (x, la, gamma) ps <-> lookahead_for la x gamma g.
(*
Definition entries_correct_wrt_production g es x gamma :=
  forall la, In (x, la, gamma) es <-> lookahead_for la x gamma g.
 *)

(* invariant relating a list of entries to a list of productions *)
Definition entries_correct_wrt_productions es ps g :=
  forall x la gamma,
    In (x, la, gamma) es <-> In (x, gamma) ps /\ lookahead_for la x gamma g.

(*
Inductive entries_correct_wrt_productions (g : grammar) :
  list pt_entry -> list production -> Prop :=
| EntriesCorrect_nil : 
    entries_correct_wrt_productions g nil nil
| EntriesCorrect_cons :
    forall front_entries back_entries x gamma ps,
      entries_correct_wrt_productions g back_entries ps
      -> entries_correct_wrt_production g front_entries x gamma
      -> entries_correct_wrt_productions g (front_entries ++ back_entries) ((x, gamma) :: ps).
 *)

Lemma invariant_iff_pt_entries_correct :
  forall es g,
    entries_correct_wrt_productions es (productions g) g <-> pt_entries_correct es g.
Proof.
  intros es g.
  split; [intros Hinv | intros Hspec].
  - unfold entries_correct_wrt_productions, pt_entries_correct in *.
    intros x la gamma.
    split; [intros Hin | intros Hlf].
    + apply Hinv in Hin.
      destruct Hin; auto.
    + apply Hinv; split; auto.
      destruct Hlf; auto.
  - unfold pt_entries_correct, entries_correct_wrt_productions in *.
    intros x la gamma.
    split; [intros Hin | intros [Hin Hlf]].
    + split.
      * apply Hspec in Hin.
        destruct Hin; auto.
      * apply Hspec; auto.
    + apply Hspec; auto.
Qed.

Lemma mkParseTableEntries'_sound :
  forall g nu fi fo ps es,
    mkParseTableEntries' nu fi fo ps = es
    -> entries_correct_wrt_productions es ps g.
Proof.
  intros g nu fi fo ps.
  induction ps as [| p ps]; intros es Hmk.
  - simpl in *; subst.
    admit.
  - simpl in *.
    unfold entries_correct_wrt_productions.
    intros x la gamma.
    split; [intros Hin | intros [Hin Hlf]].
    + subst.
      apply in_app_or in Hin.
      destruct Hin.
      * admit. (* need a lemma about mkEntriesForProd *)
      * specialize IHps with
          (es := mkParseTableEntries' nu fi fo ps).
        unfold entries_correct_wrt_productions in IHps.
        apply IHps in H; auto.
        destruct H as [Hin Hlf].
        split; auto.
        right; auto.
    + subst.
      apply in_or_app.
      inv Hin.
      * admit. (* need lemma about mkEntriesForProd *)
      * right.
        specialize (IHps (mkParseTableEntries' nu fi fo ps)).
        unfold entries_correct_wrt_productions in IHps.
        apply IHps; auto.
Admitted.
  
Lemma mkParseTableEntries_sound :
  forall g nu fi fo es,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> mkParseTableEntries nu fi fo g = es
    -> pt_entries_correct es g.
Proof.
  intros g nu fi fo es Hnu Hfi Hfo Hmk.
  apply invariant_iff_pt_entries_correct.
  unfold mkParseTableEntries in Hmk.
  eapply mkParseTableEntries'_sound; eauto.
Qed.
    
    