Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof.

Lemma forest_fuel_tree_S_fuel :
  forall g tbl gamma input fuel suffix subtrees ntName,
    isParseTableFor tbl g
    -> In (NT ntName, gamma) g
    -> parseForest tbl gamma input fuel =
       (Some subtrees, suffix)
    -> parse tbl (NT ntName) input (S fuel) =
       (Some (Node ntName subtrees), suffix).
Proof.
  intros.
  destruct fuel as [| fuel].
  - inv H1.
  - destruct gamma as [| sym gamma'].
    + (* gamma is nil *)
      simpl in H1. (* now we know that parseForest
                      produces an empty list of subtrees *)
      inv H1.
      destruct suffix as [| token suffix'].
      * simpl.
        (* The problem is that there's no lookahead token,
           which isn't a problem for parseForest, but IS a
           problem for parse *)
Abort.
      
Conjecture forest_fuel_tree_S_fuel :
  forall tbl gamma input fuel suffix subtrees ntName,
    parseForest tbl gamma input fuel =
    (Some subtrees, suffix)
    -> parse tbl (NT ntName) input (S fuel) =
       (Some (Node ntName subtrees), suffix).

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
            destruct (Utils.beqSym (T y) (T token)).
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
        { destruct input as [| token tokens].
          { inv Hparse. }
          { simpl; simpl in Hparse.
            destruct (parseTableLookup (NT x) (T token) tbl)
              as [gamma |].
            { destruct (parseForest tbl
                                    gamma
                                    (token :: tokens)
                                    fuel)
                as (subresult, input') eqn:HpfFuel.
              destruct subresult as [subtrees |].
              { destruct (parseForest tbl
                                      gamma
                                      (token :: tokens)
                                      fuel2)
                  as (subresult, input'') eqn:HpfFuel2.
                destruct subresult as [subtrees' |].
                { inv Hparse.
                  apply IHparseForest with (fuel2 := fuel2)
                    in HpfFuel.
                  { rewrite HpfFuel in HpfFuel2.
                    inv HpfFuel2.
                    reflexivity. }
                  { omega. }}
                { inv Hparse.
                  apply IHparseForest with (fuel2 := fuel2)
                    in HpfFuel.
                  { rewrite HpfFuel in HpfFuel2.
                    inv HpfFuel2. }
                  { omega. }}}
              { inv Hparse. }}
            { inv Hparse. }}}

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
            destruct (Utils.beqSym (T y) (T token)).
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
        { destruct input as [| token tokens].
          { inv Hparse. }
          { simpl; simpl in Hparse.
            destruct (parseTableLookup (NT x) (T token) tbl)
              as [gamma |].
            { destruct (parseForest tbl
                                    gamma
                                    (token :: tokens)
                                    fuel)
                as (subresult, input') eqn:HpfFuel.
              destruct subresult as [subtrees |].
              { destruct (parseForest tbl
                                      gamma
                                      (token :: tokens)
                                      fuel2)
                  as (subresult, input'') eqn:HpfFuel2.
                destruct subresult as [subtrees' |].
                { inv Hparse.
                  apply IHparseForest with (fuel2 := fuel2)
                    in HpfFuel.
                  { rewrite HpfFuel in HpfFuel2.
                    inv HpfFuel2.
                    reflexivity. }
                  { omega. }}
                { inv Hparse.
                  apply IHparseForest with (fuel2 := fuel2)
                    in HpfFuel.
                  { rewrite HpfFuel in HpfFuel2.
                    inv HpfFuel2. }
                  { omega. }}}
              { inv Hparse. }}
            { inv Hparse. }}}

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

Theorem parse_complete :
  forall (g   : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g ->
    forall (tr     : tree)
           (input  : list string)
           (sym    : symbol)
           (prefix suffix : list string),
      input = (prefix ++ suffix)%list ->
      (@derivesTree g) sym prefix tr ->
      exists (fuel : nat),
        parse tbl sym input fuel = (Some tr, suffix).
Proof.
  intros g tbl Htbl tr.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_mutual_ind with
      (P := fun tr =>
              forall input sym prefix suffix,
                input = (prefix ++ suffix)%list ->
                (@derivesTree g) sym prefix tr ->
                exists (fuel : nat),
                  parse tbl sym input fuel = (Some tr, suffix))
      (P0 := fun subtrees =>
               forall input gamma prefix suffix,
                 input = (prefix ++ suffix)%list ->
                 (@derivesForest g) gamma prefix subtrees ->
                 exists fuel,
                   parseForest tbl gamma input fuel = (Some subtrees, suffix)).
  
  - intros input sym prefix suffix Hinput HderivesTree.
    inv HderivesTree.
    exists 1. simpl.
    destruct (Utils.beqSym (T s) (T s)) eqn:Hbeq.
    + reflexivity.
    + unfold Utils.beqSym in Hbeq.
      destruct (SymbolMapFacts.eq_dec) in Hbeq.
      * inv Hbeq.
      * exfalso. apply n. reflexivity.
        
  - intros input sym prefix suffix Hinput HderivesTree.
    inv HderivesTree.
    apply IHparseForest with (prefix := prefix)
                             (suffix := suffix)
                             (input := app prefix suffix)
      in H4; clear IHparseForest.
    + destruct H4 as [fuel].
      exists (S fuel).
      eapply forest_fuel_tree_S_fuel. eassumption.
    + reflexivity.
      
  - intros input gamma prefix suffix Hinput HderivesForest.
    inv HderivesForest.
    exists 1. simpl. reflexivity.
    
  - intros input gamma prefix suffix Hinput HderivesForest.
    inv HderivesForest.
    apply IHparse with
        (input := ((prefix0 ++ suffix0)%list ++ suffix)%list)
        (suffix := (suffix0 ++ suffix)%list) in H3;
      clear IHparse.
    + destruct H3 as [hdFuel].
      apply IHparseForest with
      (input := (suffix0 ++ suffix)%list)
          (suffix := suffix) in H4; clear IHparseForest.
      * destruct H4 as [tlFuel].
        apply parse_fuel_max with (fuel2 := tlFuel) in H.
        apply parseForest_fuel_max
          with (fuel2 := hdFuel) (fuel := tlFuel) in H0.
        rewrite Max.max_comm in H0.
        exists (S (Nat.max hdFuel tlFuel)).
        simpl.
        destruct (parse tbl
                        hdRoot
                        ((prefix0 ++ suffix0) ++ suffix)
                        (Nat.max hdFuel tlFuel))
          as (subresult, input') eqn:H_hd.
        destruct subresult as [lSib |].
        { destruct (parseForest tbl
                                tlRoots
                                input'
                                (Nat.max hdFuel tlFuel))
            as (subresult, input'') eqn:H_tl.
          destruct subresult as [rSibs |].
          { inv H. rewrite H0 in H_tl.
            inv H_tl. reflexivity. }
          { inv H. rewrite H0 in H_tl. inv H_tl. }}
        { inv H. }
      * reflexivity.
    + rewrite <- app_assoc. reflexivity.
Qed.
