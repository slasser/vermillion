Require Import Lib.Grammar.

Require Import LL1.ParseTableGen.
Require Import LL1.ParseTable.

Require Import LL1.Proofs.ParseTableGen.mkNullableSet_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkFirstMap_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkFollowMap_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkEntries_Correctness.
Require Import LL1.Proofs.ParseTableGen.mkParseTable_Correctness.

(* Combining all of the steps into a single function *)

Definition parseTableOf (g : grammar) : option parse_table :=
  let nu := mkNullableSet g in
  let nu_pf := (mkNullableSet_correct g) in
  let fi := mkFirstMap g nu in
  let fi_pf := (mkFirstMap_correct g nu nu_pf) in
  let fo := mkFollowMap g nu fi fi_pf in
  let es := mkEntries nu fi fo g in
  mkParseTable es.

Theorem parseTableOf_sound : 
  forall (g : grammar) (tbl : parse_table), 
    parseTableOf g = Some tbl -> parse_table_for tbl g.
Proof.
  intros g tbl Hf.
  eapply mkParseTable_sound; eauto.
  eapply mkEntries_correct; eauto.
  - apply mkNullableSet_correct; auto.
  - apply mkFirstMap_correct.
    apply mkNullableSet_correct; auto.
  - apply mkFollowMap_correct; auto.
    apply mkNullableSet_correct; auto.
Qed.

Theorem parseTableOf_complete :
  forall (g : grammar) (tbl : parse_table),
    parse_table_for tbl g 
    -> exists (tbl' : parse_table),
      ParseTable.Equal tbl tbl' /\ parseTableOf g = Some tbl'.
Proof.
  intros g tbl Hpt.
  eapply mkParseTable_complete; eauto.
  eapply mkEntries_correct; eauto.
  - apply mkNullableSet_correct; auto.
  - apply mkFirstMap_correct.
    apply mkNullableSet_correct; auto.
  - apply mkFollowMap_correct; auto.
    apply mkNullableSet_correct; auto.
Qed.

