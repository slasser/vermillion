Require Import LL1.ParseTableGen.
Require Import LL1.ParseTable.

Require Import LL1.Proofs.ParseTableGen.mkEntries_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkParseTable_Correctness.

Theorem genTableForGrammar_sound : 
  forall g nu fi fo tbl,
  nullable_set_for nu g
  -> first_map_for fi g
  -> follow_map_for fo g
  -> genTableForGrammar g nu fi fo = Some tbl
  -> parse_table_for tbl g.
Proof.
  intros g nu fi fo tbl Hnu Hfi Hfo Hmk.
  eapply mkParseTable_sound; eauto.
  eapply mkEntries_correct; eauto.
Qed.

Theorem genTableForGrammar_complete :
  forall g nu fi fo tbl,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ genTableForGrammar g nu fi fo = Some tbl'.
Proof.
  intros g nu fi fo tbl Hnu Hfi Hfo Hpt.
  eapply mkParseTable_complete; eauto.
  eapply mkEntries_correct; eauto.
Qed.

