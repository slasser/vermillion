Require Import List Omega String.
Require Import Lib.Derivation Lib.Grammar Lib.Lemmas
               Lib.ParseTree Lib.Tactics.
Require Import LL1.CorrectnessProof. (* move lemmas out *)
Require Import LL1.ParseTable LL1.Parser.

Lemma parse_fuel_monotonic :
  forall tr tbl sym input suffix fuel fuel2,
    parse tbl sym input fuel = (Some tr, suffix)
    -> fuel < fuel2
    -> parse tbl sym input fuel2 = (Some tr, suffix).
Proof.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_mutual_ind with
      (P := fun tr =>
              forall tbl sym input suffix fuel fuel2,
                parse tbl sym input fuel = (Some tr, suffix)
                -> fuel < fuel2
                -> parse tbl sym input fuel2 =
                   (Some tr, suffix))
      (P0 := fun subtrees =>
               forall tbl gamma input suffix fuel fuel2,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, suffix)
                 -> fuel < fuel2
                 -> parseForest tbl gamma input fuel2 =
                    (Some subtrees, suffix)).
  
  - intros tbl sym input suffix fuel fuel2 Hparse Hfuel.
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
        { apply nt_derives_Node in Hparse. inv Hparse. }

  - intros tbl sym input suffix fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct sym as [y | x].
        { apply t_derives_Leaf in Hparse. inv Hparse. }
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

  - intros tbl gamma input suffix fuel fuel2 Hparse Hfuel.
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

  - intros tbl gamma input suffix fuel fuel2 Hparse Hfuel.
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
  forall sts tbl gamma input suffix fuel fuel2,
    parseForest tbl gamma input fuel = (Some sts, suffix)
    -> fuel < fuel2
    -> parseForest tbl gamma input fuel2 = (Some sts, suffix).
Proof.
  induction sts as [ s
                   | s f IHparseForest
                   |
                   | tr IHparse f IHparseForest ]
      using forest_mutual_ind with
      (P := fun tr =>
              forall tbl sym input suffix fuel fuel2,
                parse tbl sym input fuel = (Some tr, suffix)
                -> fuel < fuel2
                -> parse tbl sym input fuel2 =
                   (Some tr, suffix))
      (P0 := fun subtrees =>
               forall tbl gamma input suffix fuel fuel2,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, suffix)
                 -> fuel < fuel2
                 -> parseForest tbl gamma input fuel2 =
                    (Some subtrees, suffix)).
  
  - intros tbl sym input suffix fuel fuel2 Hparse Hfuel.
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
        { apply nt_derives_Node in Hparse. inv Hparse. }

  - intros tbl sym input suffix fuel fuel2 Hparse Hfuel.
    destruct fuel.
    + inv Hparse.
    + destruct fuel2.
      * inv Hfuel.
      * destruct sym as [y | x].
        { apply t_derives_Leaf in Hparse. inv Hparse. }
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

  - intros tbl gamma input suffix fuel fuel2 Hparse Hfuel.
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

  - intros tbl gamma input suffix fuel fuel2 Hparse Hfuel.
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
  forall fuel tbl sym input fuel2 tr suffix,
    parse tbl sym input fuel = (Some tr, suffix) ->
    parse tbl sym input (max fuel fuel2) = (Some tr, suffix).
Proof.
  intros. 
  pose proof (Max.max_spec fuel fuel2) as H_max_spec.
  destruct H_max_spec.
  - destruct H0. rewrite H1.
    eapply parse_fuel_monotonic.
    + eassumption.
    + assumption.
  - destruct H0. rewrite H1. assumption.
Qed.

Lemma parseForest_fuel_max :
  forall tbl gamma input fuel fuel2 sts suffix,
    parseForest tbl gamma input fuel = (Some sts, suffix)
    -> parseForest tbl gamma input (max fuel fuel2) =
       (Some sts, suffix).
Proof.
  intros. pose proof (Max.max_spec fuel fuel2) as H_max_spec.
  destruct H_max_spec.
  - destruct H0. rewrite H1.
    eapply parseForest_fuel_monotonic.
    + eassumption.
    + assumption.
  - destruct H0. rewrite H1. assumption.
Qed.
