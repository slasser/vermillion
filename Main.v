Require Import List.
Require Import String.
Require Import Grammar.
Require Import NoDupDec.
Require Import Tactics.
Require Import mkParseTable_correct.
Require Import Parser_complete.

Module Make (Import G : Grammar.T).

  Module Import GeneratorAndProofs := GeneratorProofsFn G.
  Module Import ParserAndProofs    := ParserProofsFn G.

  Definition parseTableOf (g : grammar) : Datatypes.sum string parse_table :=
    match findDup _ production_eq_dec (prodsOf g) with
    | Some p => inl (dupMessage p)
    | None   => 
      let nu    := mkNullableSet g in
      let nu_pf := mkNullableSet_correct g in
      let fi    := mkFirstMap g nu in
      let fi_pf := mkFirstMap_correct g nu nu_pf in
      let fo    := mkFollowMap g nu fi fi_pf in
      let es    := mkEntries nu fi fo g in
      mkParseTable es
    end.

  Theorem parseTableOf_sound : 
    forall (g : grammar) (tbl : parse_table),
      parseTableOf g = inr tbl
      -> parse_table_correct tbl g.
  Proof.
    intros g tbl Hf; unfold parseTableOf in Hf.
    step_eq Hu; tc.
    apply NoDup_findDup_None_iff in Hu.
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
      unique_productions g
      -> parse_table_correct tbl g 
      -> exists (tbl' : parse_table),
        ParseTable.Equal tbl tbl' /\ parseTableOf g = inr tbl'.
  Proof.
    intros g tbl Hu Ht.
    unfold unique_productions in Hu; unfold parseTableOf.
    pose proof Hu as Hu'; eapply NoDup_findDup_None_iff in Hu'; rewrite Hu'.
    eapply mkParseTable_complete; eauto.
    eapply mkEntries_correct; eauto.
    - apply mkNullableSet_correct; auto.
    - apply mkFirstMap_correct.
      apply mkNullableSet_correct; auto.
    - apply mkFollowMap_correct; auto.
      apply mkNullableSet_correct; auto.
  Qed.

  Definition parse (tbl : parse_table)
                   (s   : symbol)
                   (ts  : list token) :
    Datatypes.sum parse_failure (symbol_semty s * list token) :=
    match parseSymbol tbl s ts NtSet.empty (triple_lt_wf _) with
    | inl failure => inl failure
    | inr (v, existT _ ts' _) => inr (v, ts')
    end.

  Theorem parse_sound :
    forall (g   : grammar)
           (tbl : parse_table)
           (s   : symbol)
           (w r : list token)
           (v   : symbol_semty s),
      parse_table_correct tbl g
      -> parse tbl s (w ++ r) = inr (v, r)
      -> sym_derives_prefix g s w v r.
  Proof.
    intros g tbl s w r v Ht Hp.
    unfold parse in Hp.
    step_eq Hp'; tc.
    dms; invh.
    eapply parseSymbol_sound in Hp'; eauto.
    destruct Hp' as [w' [Happ Hder]].
    apply app_inv_tail in Happ; subst; auto.
  Qed.

  Theorem parse_terminates_without_error :
    forall (g      : grammar)
           (tbl    : parse_table)
           (s      : symbol)
           (ts ts' : list token)
           (m      : string)
           (x      : nonterminal),
      parse_table_correct tbl g
      -> ~ parse tbl s ts = inl (Error m x ts').
  Proof.
    unfold not; intros g tbl s ts ts' m x Ht Hp.
    unfold parse in Hp.
    step_eq Hp'; dms; tc.
    invh.
    eapply error_conditions with (sa := F_arg s) in Hp'; eauto.
    destruct Hp' as [Hf | Hex]; try ND.fsetdec.
    destruct Hex.
    eapply LL1_parse_table_impl_no_left_recursion; eauto.
  Qed.

  Theorem parse_complete :
    forall (g   : grammar)
           (tbl : parse_table)
           (s   : symbol)
           (w r : list token)
           (v   : symbol_semty s),
      parse_table_correct tbl g
      -> sym_derives_prefix g s w v r
      -> parse tbl s (w ++ r) = inr (v, r).
  Proof.
    intros g tbl s w r v Ht Hd.
    eapply parseSymbol_complete_or_error in Hd; eauto.
    destruct Hd as [Herr | Hp].
    - exfalso.
      destruct Herr as [m [x [ts' Hp]]].
      eapply parse_terminates_without_error; eauto.
      unfold parse.
      rewrite Hp; auto.
    - destruct Hp as [Hle Hp].
      unfold parse; rewrite Hp; auto.
  Qed.
  
End Make.

