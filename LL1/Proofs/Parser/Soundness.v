Require Import List.
Require Import String.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.
Require Import Lib.Utils.

Require Import LL1.Derivation.
Require Import LL1.Parser.
Require Import LL1.ParseTable.
Require Import LL1.Proofs.Lemmas.

Import ListNotations.

Lemma parse_correct' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              (fuel      : nat),
      parse tbl sym input fuel = (Some tr, rem)
      -> exists word,
        word ++ rem = input
        /\ (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr. 
  induction tr as [ s
                  | s f IHpf
                  |
                  | tr IHp f IHpf ]
                    using tree_nested_ind with
      
      (P := fun tr =>
              forall sym input rem fuel,
                parse tbl sym input fuel =
                (Some tr, rem)
                -> exists word,
                  app word rem = input
                  /\ sym_derives_prefix sym word tr rem)
      
      (Q := fun f =>
               forall gamma input rem fuel,
                 parseForest tbl gamma input fuel =
                 (Some f, rem)
                 -> exists word,
                   word ++ rem = input
                   /\ gamma_derives_prefix gamma word f rem).

  - (* T case *)
    intros sym input rem fuel Hp.
    destruct fuel as [| fuel].
    + inv Hp.
    + destruct sym as [y | x].
      * destruct input as [| tok toks]; simpl in *.
        -- inv Hp.
        -- destruct (beqString y tok) eqn:Hbeq.
           ++ inv Hp.
              exists [tok]; split; auto.
              apply beqString_eq in Hbeq.
              rewrite Hbeq; constructor.
           ++ inv Hp.
      * apply parse_nt_ret_node in Hp; inv Hp.

  - (* NT case *)
    intros sym input rem fuel Hp.
    destruct fuel as [| fuel].
    + inv Hp.
    + destruct sym as [y | x].
      * apply parse_t_ret_leaf in Hp; inv Hp.
      * simpl in Hp. 
        destruct (pt_lookup x (peek input) tbl)
          as [ys |] eqn:Hlkp.
        -- destruct (parseForest tbl ys input fuel)
            as [subres input'] eqn:Hpf.
           destruct subres as [subtrees |].
           ++ inv Hp.
              apply IHpf in Hpf; clear IHpf.
              destruct Hpf as [word].
              destruct H.
              exists word.
              split; auto.
              eapply tbl_entry_is_lookahead in Hlkp; eauto.
              econstructor; eauto.
              (* rewrite H. *) (* Why doesn't this work anymore? *)
              rewrite <- H in Hlkp.
              auto.
           ++ inv Hp.
        -- inv Hp.

  - (* nil case *)
    intros gamma input rem fuel Hpf.
    destruct fuel as [| fuel].
    + inv Hpf.
    + destruct gamma as [| hdSym tlSyms].
      * simpl in Hpf.
        inv Hpf.
        exists nil; simpl.
        split; auto.
        constructor.
      * exfalso.
        simpl in Hpf.
        destruct (parse tbl hdSym input fuel)
          as [subres input'].
        destruct subres as [lSib |].
        -- destruct (parseForest tbl tlSyms input' fuel)
            as [subres input''].
           destruct subres as [rSibs |]; inv Hpf.
        -- inv Hpf.

  - (* cons case *)
    intros gamma input rem fuel Hpf.
    destruct fuel as [| fuel].
    + inv Hpf.
    + destruct gamma as [| hdSym tlSyms]; simpl in Hpf.
      * inv Hpf.
      * destruct (parse tbl hdSym input fuel) as
            [subres input'] eqn:Hp.
        destruct subres as [lSib |].
        -- destruct (parseForest tbl tlSyms input' fuel) as
              [subres input''] eqn:Hpf'.
           destruct subres as [rSibs |].
           ++ inv Hpf.
              eapply IHp in Hp.
              destruct Hp as [wpre [Happ Hder]].
              apply IHpf in Hpf'.
              destruct Hpf' as [wsuf [Happ' Hder']].
              exists (wpre ++ wsuf).
              split.
              ** rewrite <- Happ.
                 rewrite <- Happ'.
                 rewrite app_assoc.
                 auto.
              ** econstructor; eauto.
                 (* rewrite Happ'. *) (* why doesn't this work anymore? *)
                 rewrite <- Happ' in Hder.
                 auto.
           ++ inv Hpf.
        -- inv Hpf.
Qed.

(* This version specifies exactly what prefix of the input
   is consumed *)
Theorem parse_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr       : tree)
              (sym      : symbol)
              (word rem : list string)
              (fuel     : nat),
      parse tbl sym (word ++ rem) fuel = (Some tr, rem)
      -> (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr sym word rem fuel Hp.
  pose proof Hp as Hp'.
  eapply parse_correct' in Hp; eauto.
  destruct Hp as [word' [Happ Hder]].
  apply app_inv_tail in Happ.
  subst; auto.
Qed.

