Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Definition pt_entries_correct ps g :=
  forall x la gamma,
    In (x, la, gamma) ps <-> lookahead_for la x gamma g.

Definition entries_correct_wrt_production g es x gamma :=
  forall la, In (x, la, gamma) es <-> lookahead_for la x gamma g.

(* invariant relating a list of entries to a list of productions *)
Inductive entries_correct_wrt_productions (g : grammar) :
  list pt_entry -> list production -> Prop :=
| EntriesCorrect_nil : 
    entries_correct_wrt_productions g nil nil
| EntriesCorrect_cons :
    forall front_entries back_entries x gamma ps,
      entries_correct_wrt_productions g back_entries ps
      -> entries_correct_wrt_production g front_entries x gamma
      -> entries_correct_wrt_productions g (front_entries ++ back_entries) ((x, gamma) :: ps).
    
Lemma invariant_iff_pt_entries_correct :
  forall es g,
    entries_correct_wrt_productions g es (productions g) <-> pt_entries_correct es g.
Proof.
Admitted.

Lemma mkParseTableEntries'_sound :
  forall g nu fi fo ps es,
    mkParseTableEntries' nu fi fo ps = es
    -> entries_correct_wrt_productions g es ps.
Proof.
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
    
    