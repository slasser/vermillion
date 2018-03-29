Require Import List String.
Require Import Derivation Grammar Lemmas ParseTable ParseTree LL1.Parser Lib.Tactics.

Conjecture pre_suf_nil : forall A (prefix suffix : list A),
    (prefix ++ suffix)%list = suffix ->
    prefix = nil.

Lemma tree_forest_fuel :
  forall g tbl gamma input fuel suffix subtrees ntName,
    isParseTableFor tbl g ->
    In (NT ntName, gamma) g ->
    parseForest tbl gamma input fuel = (Some subtrees, suffix) ->
    parse tbl (NT ntName) input (S fuel) = (Some (Node ntName subtrees), suffix).
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
      
Conjecture forest_fuel_tree_fuel :
  forall tbl gamma input fuel suffix subtrees ntName,
    parseForest tbl gamma input fuel =
    (Some subtrees, suffix) ->
    parse tbl (NT ntName) input (S fuel) =
    (Some (Node ntName subtrees), suffix).

Conjecture hd_fuel_tl_fuel_forest_fuel :
  forall tbl hdRoot tlRoots xs ys zs tr f fuel,
    parse tbl hdRoot (app (app xs ys) zs) fuel =
    (Some tr, app ys zs) ->
    parseForest tbl tlRoots (app ys zs) fuel = (Some f, zs) ->
    parseForest tbl (hdRoot :: tlRoots) (app (app xs ys) zs) fuel = (Some (Fcons tr f), zs).

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
      eapply forest_fuel_tree_fuel. eassumption.
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
        exists (S (hdFuel + tlFuel)).
        simpl.
        (* Here, we can prove a lemma saying that if 
           hdFuel is enough to produce the left sibling, 
           then so is (hdFuel + tlFuel), and then do the
           same thing for tlFuel *)
Abort.
