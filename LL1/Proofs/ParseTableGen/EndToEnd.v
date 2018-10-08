Require Import LL1.ParseTableGen.
Require Import LL1.ParseTable.

Require Import LL1.Proofs.ParseTableGen.mkNullableSet_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkFirstMap_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkEntries_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkParseTable_Correctness.

Theorem genTableForGrammar_sound : 
  forall g fo tbl,
  follow_map_for fo g
  -> genTableForGrammar g fo = Some tbl
  -> parse_table_for tbl g.
Proof.
  intros g fo tbl Hfo Hmk.
  eapply mkParseTable_sound; eauto.
  pose proof (mkNullableSet_correct g).
  eapply mkEntries_correct; eauto.
  apply mkFirstMap_correct; auto.
Qed.

Theorem genTableForGrammar_complete :
  forall g fo tbl,
    follow_map_for fo g
    -> parse_table_for tbl g
    -> exists tbl',
        ParseTable.Equal tbl tbl'
        /\ genTableForGrammar g fo = Some tbl'.
Proof.
  intros g fo tbl Hfo Hpt.
  eapply mkParseTable_complete; eauto.
  pose proof (mkNullableSet_correct g).
  eapply mkEntries_correct; eauto.
  apply mkFirstMap_correct; auto.
Qed.

