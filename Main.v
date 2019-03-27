Require Import Grammar.
Require Import mkParseTable_correct.
Require Import Parser_sound.

Module Main (Import G : Grammar.T).

  Module Import GeneratorProofs := GeneratorProofsFn G.
  Module Import ParserSoundness := ParserSoundnessFn G.

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
    match parse_nf tbl sym input NtSet.empty
                   (triple_lt_wf (meas tbl input NtSet.empty (F_arg sym)))
    with
    | inl failure => inl failure
    | inr (tr, existT _ input' Hle) => inr (tr, input')
    end.

  Theorem parser_sound :
    forall (g   : grammar)
           (tbl : parse_table)
           (sym : symbol)
           (word rem : list terminal)
           (tr : tree),
      parse_table_correct tbl g
      -> parse tbl sym (word ++ rem) = inr (tr, rem)
      -> (@sym_derives_prefix g) sym word tr rem.
  Proof.
    intros.
    unfold parse in *.
    destruct (parse_nf tbl sym (word ++ rem) NtSet.empty (triple_lt_wf (meas tbl (word ++ rem) NtSet.empty (F_arg sym)))) eqn:Hp.
    - tc.
    - destruct p.
      destruct s.
      inversion H0; subst.
      eapply parse_sound; eauto.  
Qed.

End Main.