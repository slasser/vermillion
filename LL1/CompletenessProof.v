Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof LL1.MonotonicityLemmas.

Conjecture in_grammar_lookup :
  forall tbl g x gamma,
    isParseTableFor tbl g
    -> In (x, gamma) g.(productions)
    -> exists lk,
        parseTableLookup x lk tbl = Some gamma.

Lemma symbol_eq_dec :
  forall (s s2 : symbol),
    {s = s2} + {~s = s2}.
Proof. repeat decide equality. Qed.

Conjecture lookup_deterministic :
  forall tbl g x lk lk',
    isParseTableFor tbl g
    ->
    (parseTableLookup x lk tbl = parseTableLookup x lk' tbl
     <-> lk = lk').

Ltac sim := simpl in *.

Definition beqSymTy s s2 :=
  match (s, s2) with
  | (T _, T _) => true
  | (NT _, NT _) => true
  | _ => false
  end.

Lemma lookup_det :
  forall tbl g lk x x',
    isParseTableFor tbl g
    -> parseTableLookup x lk tbl =
       parseTableLookup x' lk tbl
    -> x = x'.
Proof.
  intros.
  unfold parseTableLookup in H0.
Abort. (* Not true, I don't think
          X -> aY
          X -> bZ
          Y -> c
          Z -> c *)

Lemma lookup_diff :
  forall tbl g lk x x',
    isParseTableFor tbl g
    -> x <> x'
    -> parseTableLookup x lk tbl <>
       parseTableLookup x' lk tbl.
Proof.
  unfold not; intros.
  apply H0; clear H0. 
Abort.                      

Conjecture det :
  forall tbl g gamma gamma' input fuel,
    isParseTableFor tbl g
    -> parseForest tbl gamma input fuel =
       parseForest tbl gamma' input fuel
    -> gamma = gamma'.

Conjecture step :
  forall tbl g gamma input fuel f suffix x,
    isParseTableFor tbl g
    -> In (x, gamma) g.(productions)
    -> parseForest tbl gamma input fuel = (Some f, suffix)
    <-> parse tbl (NT x) input (S fuel) =
        (Some (Node x f), suffix).

Lemma lookup_ok :
  forall tbl g x gamma input fuel f suffix,
    isParseTableFor tbl g
    -> In (x, gamma) g.(productions)
    -> parseForest tbl gamma input fuel = (Some f, suffix)
    -> parseTableLookup x (peek input) tbl = Some gamma.
Proof.
  intros.
  remember H1 as H1'; clear HeqH1'.
  apply step with (g := g) (x := x) in H1.
  - simpl in H1.
    destruct (parseTableLookup x (peek input) tbl)
      as [gamma' |] eqn:Hlkp.
    + destruct (parseForest tbl gamma' input fuel)
               as (subresult, input') eqn:Hpf.
      destruct subresult as [f' |].
      * inv H1.
        rewrite <- Hpf in H1'.
        eapply det in H1'. (* NEED TO PROVE THIS! *)
        { subst. trivial. }
        { eauto. }
      * inv H1.
    + inv H1.
  - trivial.
  - trivial.
Qed.
          
Lemma unfold_parse :
  forall tbl x input fuel,
    parse tbl (NT x) input (S fuel) =
    match parseTableLookup x (peek input) tbl with
    | None => (None, input)
    | Some gamma =>
      match parseForest tbl gamma input fuel with
      | (None, _) => (None, input)
      | (Some sts, input') =>
        (Some (Node x sts), input')
      end
    end.
Proof.
  trivial.
Qed.


Conjecture lookup_parseForest :
  forall tbl g x gamma input fuel f suffix,
    isParseTableFor tbl g
    -> In (x, gamma) g.(productions)
    -> parseForest tbl gamma input fuel =
       (Some f, suffix)
    -> parseTableLookup x (peek input) tbl = Some gamma.

Lemma at_most_one_sym_succeeds :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr x input fuel suffix,
      parse tbl (NT x) input fuel = (Some tr, suffix)
      -> forall x' tr' suffix',
        x <> x'
        -> ~parse tbl (NT x') input fuel =
           (Some tr', suffix').
Proof.
  intros tbl g Htbl.
    induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_mutual_ind with
        (P := fun tr =>
                forall x input fuel suffix,
                  parse tbl (NT x) input fuel =
                  (Some tr, suffix)
                -> forall x' tr' suffix',
                  x <> x'
                  -> ~parse tbl (NT x') input fuel =
                     (Some tr', suffix'))
        
        (P0 := fun subtrees =>
                 forall gamma input fuel suffix,
                   parseForest tbl gamma input fuel =
                   (Some subtrees, suffix)
                   -> forall gamma' subtrees' suffix',
                     gamma <> gamma'
                     -> ~parseForest tbl gamma' input fuel =
                        (Some subtrees', suffix)).


  - unfold not; intros.
    apply H0.
    destruct fuel; sim.
    + inv H.
    + destruct (parseTableLookup x (peek input) tbl)
        as [gamma |] eqn:Hlkp;
        destruct (parseTableLookup x' (peek input) tbl)
        as [gamma' |] eqn:Hlkp'.
      * destruct (parseForest tbl gamma input fuel)
          as (o, input') eqn:Hpf.
        destruct (parseForest tbl gamma' input fuel)
          as (o', input'').
        destruct o; destruct o'.
        { inv H. }
        { inv H. }
        { inv H. }
        { inv H. }
      * inv H1.
      * inv H.
      * inv H.

  - unfold not; intros.
    destruct fuel; sim.
    + inv H.
    + destruct (parseTableLookup x (peek input) tbl)
        as [gamma |] eqn:Hlkp;
      destruct (parseTableLookup x' (peek input) tbl)
        as [gamma' |] eqn:Hlkp'.
      * destruct (parseForest tbl gamma input fuel)
          as (o, input') eqn:Hpf.
        destruct (parseForest tbl gamma' input fuel)
          as (o', input'') eqn:Hpf'.
        destruct o; destruct o'.
        { inv H.
          inv H1.
          eapply IHparseForest.
          { eapply Hpf. }
          { eauto. }
          { unfold not; intros.
            apply H0.
            rewrite <- H in Hpf'.
            rewrite Hpf in Hpf'.
            inv Hpf'.
            rewrite <- Hlkp in Hlkp'.
Abort. (* seems promising, though *)


Lemma derivesTree_lookup :
  forall g x prefix f,
    (@derivesTree g) (NT x) prefix (Node x f)
    -> forall tbl x suffix gamma,
    isParseTableFor tbl g
      -> parseTableLookup x (peek (prefix ++ suffix)) tbl =
         Some gamma.
Proof.
  intros g x prefix f H.
  inv H.
  intros.
  destruct prefix.
  - simpl.
Abort.

Lemma derives_exists :
  forall g x input trees,
    (@derivesTree g) (NT x) input (Node x trees)
    -> exists gamma,
      In (x, gamma) (productions g)
      /\ (@derivesForest g) gamma input trees.
Proof.
  intros.
  inv H.
  exists gamma; split; trivial.
Qed.

Lemma der_lookup :
  forall tbl g,
    isParseTableFor tbl g
    -> forall trees x input gamma,
      (@derivesTree g) (NT x) input (Node x trees)
      -> (@derivesForest g) gamma input trees
      -> parseTableLookup x (peek input) tbl = Some gamma.
Proof.
  intros tbl g Htbl trees.
  unfold isParseTableFor in Htbl.
  destruct Htbl as [Hcom Hmin].
  destruct Hcom as [Hcomfi Hcomfo].
  unfold ptCompleteFirst in Hcomfi.
  unfold ptCompleteFollow in Hcomfo.
  induction trees as [| tr trs]; intros.
  - inv H.
    inv H0.
    inv H5.
    simpl in *.

Lemma dd :
  forall trees g gamma prefix suffix x tbl,
    (@derivesForest g) gamma prefix trees
    -> (@derivesTree g) (NT x) prefix (Node x trees)
    -> isParseTableFor tbl g
    -> parseTableLookup x (peek (app prefix suffix)) tbl =
       Some gamma.
Proof.
  induction trees as [| st sts]; intros.
  - inv H.
    inv H0.
    inv H5.
    simpl.
    unfold isParseTableFor in H1.
    destruct H1 as [Hcom Hmin].
    unfold parseTableComplete in Hcom.
    destruct Hcom as [Hcomfi Hcomfo].
    unfold ptCompleteFollow in Hcomfo.
    
    apply Hcomfo with (y := EOF) in H3.
    + destruct H3 as [tMap [H3 H4]].
      unfold parseTableLookup.
      rewrite H3.
      trivial.
Admitted.

Lemma in_grammar_lookup_tbl :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma prefix suffix x fuel f,
      In (x, gamma) (productions g)
      -> parseForest tbl gamma (app prefix suffix) fuel =
         (Some f, suffix)
      -> parseTableLookup x (peek (app prefix suffix)) tbl =
         Some gamma.
Proof.
  intros tbl g Htbl gamma.
  intros.
  assert (H1 : exists (prefix' : list string),
               (app prefix' suffix) = (app prefix suffix)
               /\ (@derivesForest g) gamma prefix' f).
  { admit. }
  destruct H1 as [prefix' [H1 H2]].
  assert (prefix' = prefix).
  { admit. }
  subst.
  assert ((@derivesTree g) (NT x) prefix (Node x f)).
  { eapply derivesNT; eauto. }
  apply derives_exists in H3.

    
  induction gamma as [| sym syms]; intros.
Abort.
  
        
Conjecture in_grammar_lookup_tbl :
  forall tbl g,
    isParseTableFor tbl g
    -> forall x gamma prefix suffix fuel f,
      In (x, gamma) (productions g)
      -> parseForest tbl gamma (app prefix suffix) fuel =
         (Some f, suffix)
      -> parseTableLookup x (peek (app prefix suffix)) tbl =
         Some gamma.

(*
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
      match tr with
      | (Leaf y) => exists fuel,
                    parse tbl sym input fuel = (Some tr, suffix)
      | (Node x f) => exists fuel fuel2 gamma,
                      parseTableLookup x (peek input) tbl = Some gamma
                      /\ parseForest tbl gamma input fuel = (Some f, suffix)
                      /\ parse tbl sym input fuel2 = (Some tr, suffix)
      end.
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
              match tr with
              | (Leaf y) => exists fuel,
                            parse tbl sym input fuel = (Some tr, suffix)
              | (Node x f) => exists fuel fuel2 gamma,
                              parseTableLookup x (peek input) tbl = Some gamma
                              /\ parseForest tbl gamma input fuel = (Some f, suffix)
                              /\ parse tbl sym input fuel2 = (Some tr, suffix)
              end)
      (P0 := fun subtrees =>
               forall input gamma prefix suffix,
                     input = (prefix ++ suffix)%list ->
                     (@derivesForest g) gamma prefix subtrees ->
                     exists x fuel, parseTableLookup x (peek input) tbl= Some gamma
                                    /\ parseForest tbl gamma input fuel = (Some subtrees, suffix)).

  - intros.
    inv H0.
    exists 1.
    simpl.
    assert (Utils.beqString s s = true) by admit.
    rewrite H.
    trivial.

  - intros.
    inv H0.
    eapply IHparseForest with (prefix := prefix) (suffix := suffix) (input := app prefix suffix) in H6.
    + destruct H6 as [x [fuel [ Hl Hpf]]].
      exists fuel. exists (S fuel). exists gamma.
      split.
      * trivial.
*)

Theorem parse_complete :
  forall (g   : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g ->
    forall (tr     : tree)
           (input  : list string)
           (sym    : symbol)
           (prefix suffix : list string),
      input = (prefix ++ suffix)%list ->
      derivesMaximalTree g sym prefix suffix tr
      -> exists (fuel : nat),
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
                derivesMaximalTree g sym prefix suffix tr
                -> exists (fuel : nat),
                    parse tbl sym input fuel =
                    (Some tr, suffix))

      (P0 := fun subtrees =>
               forall input gamma prefix suffix,
                 input = (prefix ++ suffix)%list
                 -> (@derivesForest g) gamma prefix subtrees
                 -> exists fuel,
                     parseForest tbl gamma input fuel =
                     (Some subtrees, suffix)).

  - intros input sym prefix suffix Hinput HderivesTree.
    inv HderivesTree.
    inv H.
    exists 1. simpl.
    destruct (Utils.beqString s s) eqn:Hbeq.
    + reflexivity.
    + unfold Utils.beqString in Hbeq.
      destruct (StringMapFacts.eq_dec) in Hbeq.
      * inv Hbeq.
      * exfalso. apply n. reflexivity.

  (* hard case *)
  - intros input sym prefix suffix Hinput HderivesTree.
    inv HderivesTree.
    inv H.
    apply IHparseForest with (prefix := prefix)
                             (suffix := suffix)
                             (input := app prefix suffix)
      in H6; clear IHparseForest; eauto.
    destruct H6 as [fuel].
    
    + destruct H4 as [fuel].
      exists (S fuel).
      simpl.
      destruct (parseTableLookup s
                                 (peek (prefix ++ suffix)) tbl)
        as [gamma' |] eqn:Hlkp.
      * destruct (parseForest tbl gamma' (prefix ++ suffix)
                              fuel)
          as (o, suffix') eqn:Hpf.
        destruct o as [f' |].
        -- unfold parseTableLookup in Hlkp.
           
      eapply in_grammar_lookup_tbl in Htbl; eauto.
      rewrite Htbl.
      rewrite H.
      trivial.

  - intros x input gamma prefix suffix Hinput HderivesForest.
    inv HderivesForest.
    exists 1. simpl. trivial.
      
  - intros x input gamma prefix suffix Hinput HderivesForest.
    inv HderivesForest.
    apply IHparse with
        (input := ((prefix0 ++ suffix0)%list ++ suffix)%list)
        (suffix := (suffix0 ++ suffix)%list) in H3;
      clear IHparse.
    + destruct H3 as [hdFuel].
      
      apply IHparseForest with
      (input := (suffix0 ++ suffix)%list)
      (suffix := suffix)
       in H4; clear IHparseForest.
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
            inv H_tl.
            split; try trivial. }
          { inv H. congruence. }}
        { inv H. }
      * trivial.
      * trivial.
    + rewrite <- app_assoc. reflexivity.
Qed.

(* - Doing induction on the right thing?
   - Look at example of inductive proof using fuel *)
