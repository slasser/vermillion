Require Import List.
Require Import String.

Require Import Grammar.
Require Import Tactics.

Require Import Parser.
Require Import Lemmas.

Require Import Parser_complete.

Module DetFn (Import G : Grammar.T).

  Module Import ParserProofs := ParserProofsFn G.
  
  Lemma LL1_derivation_deterministic :
    forall (tbl : parse_table)
           (g : grammar),
      parse_table_correct tbl g
      -> forall (sym : symbol)
                (word rem : list terminal)
                (tr : tree),
        (@sym_derives_prefix g) sym word tr rem
        -> forall (word' rem' : list terminal)
                  (tr' : tree),
          (@sym_derives_prefix g) sym word' tr' rem'
          -> word ++ rem = word' ++ rem'
          -> word = word' /\ rem = rem' /\ tr = tr'.
Proof.
  intros tbl g Htbl sym word  rem  tr  Hder
         word' rem' tr' Hder' Heq.
  eapply parse_nf_complete in Hder;  eauto.
  rewrite Heq in Hder.
  eapply parse_nf_complete in Hder'; eauto.
  destruct Hder as [Hle Hp].
  destruct Hder' as [Hle' Hp'].
  rewrite Hp in Hp'.
  inv Hp'.
  apply app_inv_tail in Heq; subst; auto.
Qed.

End DetFn.