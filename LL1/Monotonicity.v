Require Import Arith.
Require Import Omega.
Require Import String.

Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.

Require Import LL1.Lemmas.
Require Import LL1.Parser.
Require Import LL1.ParseTable.

Lemma parse_fuel_monotonic :
  forall (tr : tree)
         (tbl : parse_table)
         (sym : symbol)
         (input rem : list string)
         (fuel fuel2 : nat),
    parse tbl sym input fuel = (Some tr, rem)
    -> fuel < fuel2
    -> parse tbl sym input fuel2 = (Some tr, rem).
Proof.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
                    using tree_nested_ind with
      
      (P := fun tr =>
              forall tbl sym input rem fuel fuel2,
                parse tbl sym input fuel = (Some tr, rem)
                -> fuel < fuel2
                -> parse tbl sym input fuel2 = (Some tr, rem))
      
      (Q := fun subtrees =>
              forall tbl gamma input rem fuel fuel2,
                parseForest tbl gamma input fuel =
                 (Some subtrees, rem)
                 -> fuel < fuel2
                 -> parseForest tbl gamma input fuel2 = (Some subtrees, rem)).

  
  - (* simplify other bullets to look like this one *)
    intros tbl sym input rem fuel fuel2 Hparse Hfuel.
    destruct fuel;  try solve [inv Hparse].
    destruct fuel2; try solve [inv Hfuel].
    destruct sym as [y | x].
    + destruct input as [| token tokens]; try solve [inv Hparse].
      simpl in *. 
      destruct (Utils.beqString y token); inv Hparse; auto.
    + apply parse_nt_ret_node in Hparse; inv Hparse.
           
  - intros tbl sym input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct sym as [y | x].
        -- apply parse_t_ret_leaf in Hparse. inv Hparse.
        -- simpl; simpl in Hparse.
           destruct (parseTableLookup x (peek input) tbl)
            as [gamma |] eqn:Hlookup.
           ++ destruct (parseForest tbl gamma input fuel)
               as (subresult, input') eqn:Hpf.
              destruct subresult as [subtrees |].
              ** inv Hparse.
                 apply IHparseForest with (fuel2 := fuel2)
                   in Hpf; clear IHparseForest.
                 --- destruct (parseForest tbl gamma input fuel2)
                     as (subresult, input') eqn:Hpf2.
                     destruct subresult as [subtrees |].
                     +++ congruence.
                     +++ inv Hpf.
              --- apply lt_S_n. assumption.
              ** inv Hparse.
           ++ inv Hparse.

  - intros tbl gamma input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct gamma as [| sym syms].
        { simpl. inv Hparse. reflexivity. }
        (* Maybe prove in a separate lemma that 
           a non-empty gamma never derives Fnil *)
        { simpl in Hparse.
          destruct (parse tbl sym input fuel)
            as (subresult, input').
          destruct subresult as [lSib |].
          { destruct (parseForest tbl syms input' fuel)
              as (subresult, input'').
            destruct subresult as [rSibs |].
            { inv Hparse. }
            { inv Hparse. }}
          { inv Hparse. }}

  - intros tbl gamma input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct gamma as [| sym syms].
        { inv Hparse. }
        { simpl; simpl in Hparse.
          destruct (parse tbl sym input fuel)
            as (subresult, input') eqn:HparseFuel.
          { destruct subresult as [lSib |].
            { destruct (parseForest tbl syms input' fuel)
                as (subresult, input'') eqn:HparseForestFuel.
              destruct subresult as [rSibs |].
              { destruct (parse tbl sym input fuel2)
                  as (subresult, input2') eqn:HparseFuel2.
                { destruct subresult as [lSib2 |].
                  { destruct (parseForest tbl syms input2' fuel2) as (subresult, input2'') eqn:HparseForestFuel2.
                    destruct subresult as [rSibs2 |].
                    { inv Hparse.
                      apply IHparse with (fuel2 := fuel2)
                        in HparseFuel.
                      { rewrite HparseFuel in HparseFuel2.
                        inv HparseFuel2.
                        apply IHparseForest
                          with (fuel2 := fuel2)
                          in HparseForestFuel.
                        { rewrite HparseForestFuel in HparseForestFuel2.
                          inv HparseForestFuel2.
                          reflexivity. }
                        { omega. }}
                      { omega. }}
                    { inv Hparse.
                      apply IHparse
                        with (fuel2 := fuel2)
                        in HparseFuel.
                      { rewrite HparseFuel in HparseFuel2.
                        inv HparseFuel2.
                        apply IHparseForest
                          with (fuel2 := fuel2)
                        in HparseForestFuel.
                        { rewrite HparseForestFuel
                          in HparseForestFuel2.
                          inv HparseForestFuel2. }
                        { omega. }}
                      { omega. }}}
                  { inv Hparse.
                    apply IHparse
                      with (fuel2 := fuel2)
                      in HparseFuel.
                    { rewrite HparseFuel in HparseFuel2.
                      inv HparseFuel2. }
                    { omega. }}}}
              { inv Hparse. }}
            { inv Hparse. }}}
Qed.

Lemma parseForest_fuel_monotonic :
  forall sts tbl gamma input rem fuel fuel2,
    parseForest tbl gamma input fuel = (Some sts, rem)
    -> fuel < fuel2
    -> parseForest tbl gamma input fuel2 = (Some sts, rem).
Proof.
  induction sts as [ s
                   | s f IHparseForest
                   |
                   | tr IHparse f IHparseForest ]
      using forest_nested_ind with
      (P := fun tr =>
              forall tbl sym input rem fuel fuel2,
                parse tbl sym input fuel = (Some tr, rem)
                -> fuel < fuel2
                -> parse tbl sym input fuel2 =
                   (Some tr, rem))
      (Q := fun subtrees =>
               forall tbl gamma input rem fuel fuel2,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, rem)
                 -> fuel < fuel2
                 -> parseForest tbl gamma input fuel2 =
                    (Some subtrees, rem)).
  
  - intros tbl sym input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct sym as [y | x].
        { destruct input as [| token tokens].
          { inv Hparse. }
          { simpl; simpl in Hparse.
            destruct (Utils.beqString y token).
            { inv Hparse. reflexivity. }
            { inv Hparse. }}}
        { apply parse_nt_ret_node in Hparse. inv Hparse. }

  - intros tbl sym input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct sym as [y | x].
        { apply parse_t_ret_leaf in Hparse. inv Hparse. }
        { simpl; simpl in Hparse.
          destruct (parseTableLookup x (peek input) tbl)
            as [gamma |] eqn:Hlookup.
          { destruct (parseForest tbl gamma input fuel)
              as (subresult, input') eqn:Hpf.
            destruct subresult as [subtrees |].
            { inv Hparse.
              apply IHparseForest with (fuel2 := fuel2)in Hpf;
              clear IHparseForest.
              { destruct (parseForest tbl gamma input fuel2)
                  as (subresult, input') eqn:Hpf2.
                destruct subresult as [subtrees |].
                { congruence. }
                { inv Hpf. }}
              { apply lt_S_n. assumption. }}
            { inv Hparse. }}
          { inv Hparse. }}

  - intros tbl gamma input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct gamma as [| sym syms].
        { simpl. inv Hparse. reflexivity. }
        (* Maybe prove in a separate lemma that 
           a non-empty gamma never derives Fnil *)
        { simpl in Hparse.
          destruct (parse tbl sym input fuel)
            as (subresult, input').
          destruct subresult as [lSib |].
          { destruct (parseForest tbl syms input' fuel)
              as (subresult, input'').
            destruct subresult as [rSibs |].
            { inv Hparse. }
            { inv Hparse. }}
          { inv Hparse. }}

  - intros tbl gamma input rem fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct gamma as [| sym syms].
        { inv Hparse. }
        { simpl; simpl in Hparse.
          destruct (parse tbl sym input fuel)
            as (subresult, input') eqn:HparseFuel.
          { destruct subresult as [lSib |].
            { destruct (parseForest tbl syms input' fuel)
                as (subresult, input'') eqn:HparseForestFuel.
              destruct subresult as [rSibs |].
              { destruct (parse tbl sym input fuel2)
                  as (subresult, input2') eqn:HparseFuel2.
                { destruct subresult as [lSib2 |].
                  { destruct (parseForest tbl syms input2' fuel2) as (subresult, input2'') eqn:HparseForestFuel2.
                    destruct subresult as [rSibs2 |].
                    { inv Hparse.
                      apply IHparse with (fuel2 := fuel2)
                        in HparseFuel.
                      { rewrite HparseFuel in HparseFuel2.
                        inv HparseFuel2.
                        apply IHparseForest
                          with (fuel2 := fuel2)
                          in HparseForestFuel.
                        { rewrite HparseForestFuel in HparseForestFuel2.
                          inv HparseForestFuel2.
                          reflexivity. }
                        { omega. }}
                      { omega. }}
                    { inv Hparse.
                      apply IHparse
                        with (fuel2 := fuel2)
                        in HparseFuel.
                      { rewrite HparseFuel in HparseFuel2.
                        inv HparseFuel2.
                        apply IHparseForest
                          with (fuel2 := fuel2)
                        in HparseForestFuel.
                        { rewrite HparseForestFuel
                          in HparseForestFuel2.
                          inv HparseForestFuel2. }
                        { omega. }}
                      { omega. }}}
                  { inv Hparse.
                    apply IHparse
                      with (fuel2 := fuel2)
                      in HparseFuel.
                    { rewrite HparseFuel in HparseFuel2.
                      inv HparseFuel2. }
                    { omega. }}}}
              { inv Hparse. }}
            { inv Hparse. }}}
Qed. (* Hmm...same proof as the one for parse! *)

Lemma parse_fuel_max :
  forall fuel tbl sym input fuel2 tr rem,
    parse tbl sym input fuel = (Some tr, rem) ->
    parse tbl sym input (max fuel fuel2) = (Some tr, rem).
Proof.
  intros. 
  pose proof (Max.max_spec fuel fuel2) as H_max_spec.
  destruct H_max_spec.
  - destruct H0. rewrite H1.
    eapply parse_fuel_monotonic; eauto.
  - destruct H0. rewrite H1. auto.
Qed.

Lemma parseForest_fuel_max :
  forall tbl gamma input fuel fuel2 sts rem,
    parseForest tbl gamma input fuel = (Some sts, rem)
    -> parseForest tbl gamma input (max fuel fuel2) =
       (Some sts, rem).
Proof.
  intros.
  pose proof (Max.max_spec fuel fuel2) as H_max_spec.
  destruct H_max_spec.
  - destruct H0. rewrite H1.
    eapply parseForest_fuel_monotonic; eauto.
  - destruct H0. rewrite H1. auto.
Qed.
