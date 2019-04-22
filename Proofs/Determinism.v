Require Import List.
Require Import String.

Require Import Grammar.
Require Import Tactics.

Require Import Main.

Module DetFn (Import G : Grammar.T).

  Module Import PG := Make G.

  Corollary LL1_derivation_deterministic :
    forall (g         : grammar)
           (tbl       : parse_table)
           (s         : symbol)
           (w w' r r' : list token)
           (v v'      : symbol_semty s),
      parse_table_correct tbl g
      -> w ++ r = w' ++ r'
      -> sym_derives_prefix g s w  v  r
      -> sym_derives_prefix g s w' v' r'
      -> w = w' /\ r = r' /\ v = v'.
  Proof.
    intros g tbl s w w' r r' v v' Ht Heq Hd Hd'.
    eapply parse_complete in Hd;  eauto.
    eapply parse_complete in Hd'; eauto.
    rewrite Heq in Hd; rewrite Hd in Hd'; inv Hd'.
    apply app_inv_tail in Heq; subst; auto.
  Qed.

End DetFn.

