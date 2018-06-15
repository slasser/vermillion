Require Import List Omega String.
Require Import ExampleGrammars Grammar
               Lemmas LL1.Parser Lib.Tactics ParseTable
               ParseTree Lib.Utils LL1.LL1_Derivation.
Import ListNotations.
Open Scope list_scope.

Lemma beqString_eq : 
  forall s s2,
    beqString s s2 = true
    -> s = s2.
Proof.
  intros; unfold beqString in H.
  destruct (StringMapFacts.eq_dec s s2); trivial.
  inv H.
Qed.

Lemma parse_t_ret_leaf :
  forall tbl y input fuel tree suffix,
    parse tbl (T y) input fuel = (Some tree, suffix) ->
    isLeaf tree = true.
Proof.
  intros. destruct fuel.
  - inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (Utils.beqString y s).
      * inv H. reflexivity.
      * inv H.
Qed.

Lemma parse_nt_ret_node :
  forall tbl x input fuel tree suffix,
    parse tbl (NT x) input fuel = (Some tree, suffix)
    -> isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct (parseTableLookup x (peek input) tbl).
    + destruct (parseForest tbl l input fuel). 
      destruct o. 
      * inv H. trivial.
      * inv H.
    + inv H. 
Qed.

Lemma tbl_entry_is_lookahead :
  forall tbl g x la gamma,
    isParseTableFor tbl g
    -> parseTableLookup x la tbl = Some gamma
    -> (@isLookaheadFor g) la (NT x) gamma.
Proof.
  intros tbl g x la gamma Htbl Hlkp.
  destruct Htbl as [Hmin Hcom].
  unfold ptMinimal in Hmin.
  unfold parseTableLookup in Hlkp.
  destruct (StringMap.find x tbl) as [m |] eqn:Hsf.
  - eapply Hmin; eauto.
  - inv Hlkp.
Qed.

Theorem parse_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list string)
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
                    using tree_mutual_ind with
      
      (P := fun tr =>
              forall sym input rem fuel,
                parse tbl sym input fuel =
                (Some tr, rem)
                -> exists word,
                  word ++ rem = input
                  /\ sym_derives_prefix sym word tr rem)
      
      (P0 := fun f =>
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
        destruct (parseTableLookup x (peek input) tbl)
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
              rewrite H.
              auto.
           ++ inv Hp.
        -- inv Hp.

  - (* Fnil case *)
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

  - (* Fcons case *)
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
                 rewrite Happ'.
                 auto.
           ++ inv Hpf.
        -- inv Hpf.
Qed.

(* This version specifies exactly what prefix of the input
   is consumed *)
Corollary parse_correct' :
  forall (g   : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g
    -> forall (tr       : tree)
              (sym      : symbol)
              (word rem : list string)
              (fuel     : nat),
      parse tbl sym (word ++ rem) fuel = (Some tr, rem)
      -> (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr sym word rem fuel Hp.
  pose proof Hp as Hp'.
  eapply parse_correct in Hp; eauto.
  destruct Hp as [word' [Happ Hder]].
  apply app_inv_tail in Happ.
  subst; auto.
Qed.
