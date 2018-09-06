Require Import LL1.ParseTableGen.
Require Import LL1.ParseTable.

Require Import LL1.Proofs.ParseTableGen.mkNullableSet_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkEntries_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkParseTable_Correctness.

Theorem genTableForGrammar_sound : 
  forall g fi fo tbl,
  first_map_for fi g
  -> follow_map_for fo g
  -> genTableForGrammar g fi fo = Some tbl
  -> parse_table_for tbl g.
Proof.
  intros g fi fo tbl Hfi Hfo Hmk.
  eapply mkParseTable_sound; eauto.
  eapply mkEntries_correct; eauto.
  apply mkNullableSet_correct.
Qed.

Theorem genTableForGrammar_complete :
  forall g fi fo tbl,
    first_map_for fi g
    -> follow_map_for fo g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ genTableForGrammar g fi fo = Some tbl'.
Proof.
  intros g fi fo tbl Hfi Hfo Hpt.
  eapply mkParseTable_complete; eauto.
  eapply mkEntries_correct; eauto.
  apply mkNullableSet_correct.
Qed.

