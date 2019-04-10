Require Import Grammar.
Require Import Tactics.
Require Import mkParseTable_correct.
Require Import Parser_complete.

Module Make (Import G : Grammar.T).

  Module Import GeneratorAndProofs := GeneratorProofsFn G.
  Module Import ParserAndProofs    := ParserProofsFn G.

  Definition parseTableOf (g : grammar) : option parse_table :=
    let nu    := mkNullableSet g in
    let nu_pf := (mkNullableSet_correct g) in
    let fi    := mkFirstMap g nu in
    let fi_pf := (mkFirstMap_correct g nu nu_pf) in
    let fo    := mkFollowMap g nu fi fi_pf in
    let es    := mkEntries nu fi fo g in
    mkParseTable es.

  Theorem parseTableOf_sound : 
    forall (g : grammar) (tbl : parse_table), 
      parseTableOf g = Some tbl
      -> parse_table_correct tbl g.
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
      parse_table_correct tbl g 
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

  Definition parse (tbl : parse_table)
                   (sym : symbol)
                   (input : list terminal) :
    Datatypes.sum parse_failure (tree * list terminal) :=
    match parseTree tbl sym input NtSet.empty (triple_lt_wf _) with
    | inl failure => inl failure
    | inr (tr, existT _ input' _) => inr (tr, input')
    end.

  Theorem parse_sound :
    forall (g   : grammar)
           (tbl : parse_table)
           (sym : symbol)
           (word rem : list terminal)
           (tr : tree),
      parse_table_correct tbl g
      -> parse tbl sym (word ++ rem) = inr (tr, rem)
      -> sym_derives_prefix g sym word tr rem.
  Proof.
    intros g tbl sym word rem tr Ht Hp.
    unfold parse in Hp.
    step_eq Hp; tc.
    dms; invh.
    eapply parseTree_sound; eauto.
  Qed.

  Theorem parse_safe :
    forall (g   : grammar)
           (tbl : parse_table)
           (sym : symbol)
           (input : list terminal)
           (tr : tree),
      parse_table_correct tbl g
      -> forall x vis input',
        ~ parse tbl sym input = inl (LeftRec x vis input').
  Proof.
    unfold not; intros g tbl sym input tr Ht x vis input' Hp.
    unfold parse in Hp.
    step_eq Hp'; dms; tc.
    invh.
    eapply leftrec_conditions with (sa := F_arg sym) in Hp'; eauto.
    destruct Hp' as [Hf | Hex]; try ND.fsetdec.
    destruct Hex.
    eapply LL1_parse_table_impl_no_left_recursion; eauto.
  Qed.

  Theorem parse_complete :
    forall g tbl sym word tr rem,
      parse_table_correct tbl g
      -> sym_derives_prefix g sym word tr rem
      -> parse tbl sym (word ++ rem) = inr (tr, rem).
  Proof.
    intros g tbl sym word tr rem Ht Hd.
    eapply parseTree_complete_or_leftrec in Hd; eauto.
    destruct Hd as [Hlr | Hp].
    - exfalso.
      destruct Hlr as [x [vis' [input' Hp]]].
      eapply parse_safe; eauto.
      unfold parse.
      rewrite Hp; auto.
    - destruct Hp as [Hle Hp].
      unfold parse; rewrite Hp; auto.
  Qed.
  
End Make.

