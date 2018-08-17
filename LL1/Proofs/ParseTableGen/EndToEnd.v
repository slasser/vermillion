Require Import LL1.ParseTableGen.
Require Import LL1.ParseTable.

Require Import LL1.Proofs.ParseTableGen.tableFromEntries_Correctness.
Require Import LL1.Proofs.ParseTableGen.tableEntries_Correctness.

Theorem mkParseTable_sound : 
  forall g nu fi fo tbl,
  nullable_set_for nu g
  -> first_map_for fi g
  -> follow_map_for fo g
  -> mkParseTable g nu fi fo = Some tbl
  -> parse_table_for tbl g.
Proof.
  intros g nu fi fo tbl Hnu Hfi Hfo Hmk.
  eapply tableFromEntries_sound; eauto.
  eapply tableEntries_correct; eauto.
Qed.

Theorem mkParseTable_complete :
  forall g nu fi fo tbl,
    nullable_set_for nu g
    -> first_map_for fi g
    -> follow_map_for fo g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ mkParseTable g nu fi fo = Some tbl'.
Proof.
  intros g nu fi fo tbl Hnu Hfi Hfo Hpt.
  eapply tableFromEntries_complete; eauto.
  eapply tableEntries_correct; eauto.
Qed.
