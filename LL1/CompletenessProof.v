Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof LL1.MonotonicityLemmas.
Open Scope string_scope.

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

Lemma lookup_exists :
  forall x la tbl gamma,
    parseTableLookup x la tbl = Some gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.
Proof.
  intros.
  unfold parseTableLookup in H.
  destruct (StringMap.find x tbl) as [laMap |] eqn:Hsf.
  - exists laMap; split; trivial.
  - inv H.
Qed.


Lemma eof_fprod :
  forall g la x gamma,
    (@firstProd g) la x gamma
    -> la = EOF
    -> False.
Proof.
  intros g la x gamma H.
  induction H using firstProd_mutual_ind with
      (P := fun la x gamma (pf : firstProd la x gamma) =>
              la = EOF -> False)
      (P0 := fun la gamma (pf : firstGamma la gamma) =>
               la = EOF -> False)
      (P1 := fun la sym (pf : firstSym la sym) =>
               la = EOF -> False); intros.
  - apply IHfirstProd; trivial.
  - apply IHfirstProd; trivial.
  - apply IHfirstProd; trivial. 
  - inv H.
  - apply IHfirstProd; trivial.
Qed.

Import ListNotations.
Theorem parseForest_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    ParseTable.isParseTableFor tbl g ->
    forall f input gamma suffix fuel,
      parseForest tbl gamma input fuel =
      (Some f, suffix) ->
      exists prefix,
        (prefix ++ suffix)%list = input /\
        (@derivesForest g) gamma prefix f.
Proof.
  intros g tbl Htbl f.
  induction f using forest_mutual_ind with
      (P0 := fun subtrees =>
               forall input gamma suffix fuel,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees)
      (P := fun tr =>
              forall input sym suffix fuel,
                parse tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr).

  - intros input sym suffix fuel Hparse. 
    destruct fuel as [| fuel].
    + inv Hparse.
    + destruct sym as [y | x].
      * destruct input as [| token input].
        { inv Hparse. }
        simpl in Hparse.
        destruct (Utils.beqString y token) eqn:Hbeq.
        { inv Hparse. exists [token]. split.
          { reflexivity. }
          apply beqString_eq in Hbeq. subst.
          apply derivesT. }
        inv Hparse.
      * apply nt_derives_Node in Hparse. inv Hparse.

  - intros input sym suffix fuel Hparse.
    destruct fuel as [| fuel].
    + inv Hparse.
    + destruct sym as [y | x].
      * apply t_derives_Leaf in Hparse. inv Hparse.
      * simpl in Hparse. 
        destruct (parseTableLookup x (peek input) tbl)
                 as [ys |] eqn:Hlookup.
        { destruct (parseForest tbl ys input fuel)
                   as [subresult input'] eqn:Hforest.
          { destruct subresult as [subtrees |].
            { inv Hparse.
              apply IHf in Hforest.
              destruct Hforest as [prefix Hforest].
              exists prefix.
              destruct Hforest as [Happ Hderives]. split.
              { assumption. }
              inv Hderives.
              { apply derivesNT with (gamma := nil).
                { simpl in Hlookup. 
                  apply lookup_tbl_in_grammar with
                      (g := g)
                      (x := s)
                      (y := peek suffix)
                      (gamma:=nil) in Hlookup.
                  { assumption. }
                  assumption. }
                apply derivesFnil. }
              apply derivesNT with
                  (gamma := (hdRoot :: tlRoots)).
              { eapply lookup_tbl_in_grammar; eassumption. }
              { apply derivesFcons; assumption. }}
            { inv Hparse. }}}
        { inv Hparse. }

  - intros input gamma suffix fuel HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * simpl in HparseForest. inv HparseForest.
        exists nil. split.
        { reflexivity. }
        apply derivesFnil.
      * exfalso.
        simpl in HparseForest.
        destruct (parse tbl sym input fuel)
          as [subresult input'].
        destruct subresult as [lSib |].
        { destruct (parseForest tbl gamma' input' fuel)
            as [subresult input''].
          destruct subresult as [rSibs |].
          { inv HparseForest. }
          inv HparseForest. }
        inv HparseForest.

  - intros input gamma suffix fuel HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * inv HparseForest.
      * simpl in HparseForest.
        destruct (parse tbl sym input fuel)
          as [subresult input'] eqn:Htree.
        destruct subresult.
        { destruct (parseForest tbl gamma' input' fuel)
            as [subresult input''] eqn:Hforest.
          destruct subresult as [rSibs |].
          { inv HparseForest.
            apply IHf in Htree.
            { destruct Htree as [treePrefix Htree].
              destruct Htree as [HappTree HderivesTree].
              apply IHf0 in Hforest.
              destruct Hforest as [forestPrefix Hforest].
              destruct Hforest as [HappForest HderivesForest].
              subst.
              exists (treePrefix ++ forestPrefix)%list. split.
              { rewrite app_assoc. reflexivity. }
              apply derivesFcons.
              { assumption. }
              assumption. }}
          inv HparseForest. }
        inv HparseForest.
Qed.

Lemma derivesForest_nil_nullable :
  forall f g gamma,
    (@derivesForest g) gamma [] f
    -> (@nullableGamma g) gamma.
Proof.
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall g x,
                (@derivesTree g) (NT x) nil tr
                -> (@nullableSym g) (NT x))
      (P0 := fun f =>
               forall g gamma,
                 (@derivesForest g) gamma nil f
                 -> (@nullableGamma g) gamma); intros.

  - inv H.
  - inv H.
    apply IHf in H5.
    econstructor.
    econstructor; eauto.
  - inv H.
    constructor.
  - destruct gamma.
    + constructor.
    + inv H.
      assert (prefix = nil) by
          (destruct prefix; try inv H2; auto).
      assert (suffix = nil) by
          (destruct prefix; try inv H2; auto).
      subst.
      inv H4.
      constructor.
      * apply IHf.
        econstructor; eauto.
      * apply IHf0.
        auto.
Qed.

Lemma derivesTree_nil_nullable :
  forall t g x,
    (@derivesTree g) (NT x) [] t
    -> (@nullableSym g) (NT x).
Proof.
  induction t using tree_mutual_ind with
      (P := fun tr =>
              forall g x,
                (@derivesTree g) (NT x) nil tr
                -> (@nullableSym g) (NT x))
      (P0 := fun f =>
               forall g gamma,
                 (@derivesForest g) gamma nil f
                 -> (@nullableGamma g) gamma); intros.

    - inv H.
  - inv H.
    apply IHt in H5.
    econstructor.
    econstructor; eauto.
  - inv H.
    constructor.
  - destruct gamma.
    + constructor.
    + inv H.
      assert (prefix = nil) by
          (destruct prefix; try inv H2; auto).
      assert (suffix = nil) by
          (destruct prefix; try inv H2; auto).
      subst.
      inv H4.
      constructor.
      * apply IHt.
        econstructor; eauto.
      * apply IHt0.
        auto.
Qed.
    

Lemma firstProd_not_nil :
  forall tbl g,
    isParseTableFor tbl g
    -> forall f x gamma word tok,
      (@derivesForest g) gamma word f
      -> (@firstProd g) (LA tok) x gamma
      -> exists tl,
          word = tok :: tl.
Proof.
Admitted.

Lemma derivesForest_cons_firstGamma :
  forall f g tok toks gamma,
    (@derivesForest g) gamma (tok :: toks) f
    -> (@firstGamma g) (LA tok) gamma.
Proof.
  intro f.
  induction f using forest_mutual_ind with
      (P0 := fun f =>
              forall g tok toks gamma,
                (@derivesForest g) gamma (tok :: toks) f
                -> (@firstGamma g) (LA tok) gamma)
      (P := fun tr =>
               forall g tok toks x,
                 (@derivesTree g) x (tok :: toks) tr
                 -> (@firstSym g) (LA tok) x); intros.

  - inv H.
    constructor.

  - inv H.
    apply IHf with (tok := tok) (toks := toks) in H5.
    eapply FiNT.
    constructor; eauto.

  - inv H.

  - inv H.
    destruct prefix.
    + simpl in *.
      subst.
      apply IHf0 in H5.
      destruct hdRoot.
      * inv H4.
      * apply FiGammaTl.
        -- apply derivesTree_nil_nullable in H4.
           auto.
        -- auto.
    + simpl in *.
      inv H0.
      apply IHf in H4.
      apply FiGammaHd.
      auto.
Qed.

Lemma derivesForest_cons_firstProd :
  forall f g tok toks x gamma,
    In (x, gamma) (productions g)
    -> (@derivesForest g) gamma (tok :: toks) f
    -> (@firstProd g) (LA tok) x gamma.
Proof.
  intros.
  constructor; auto.
  eapply derivesForest_cons_firstGamma.
  eauto.
Qed.

Lemma prefixes_eq :
  forall (suf pre pre' : list string),
    app pre suf = app pre' suf
    -> pre = pre'.
Proof.
  induction suf; intros; simpl in *.
  - repeat rewrite app_nil_r in H.
    auto.
  - assert (a :: suf = app [a] suf) by auto.
    repeat rewrite H0 in H.
    repeat rewrite app_assoc in H.
    apply IHsuf in H.
    apply app_inj_tail in H.
    destruct H.
    auto.
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
      symDerivesMaximalPrefix g sym prefix suffix tr
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
                symDerivesMaximalPrefix g sym prefix suffix tr
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
    unfold symDerivesMaximalPrefix in HderivesTree.
    destruct HderivesTree as [Hder Hmax].
    inv Hder.
    apply IHparseForest with (prefix := prefix)
                             (suffix := suffix)
                             (input := app prefix suffix)
      in H4; clear IHparseForest; eauto.
    destruct H4 as [fuel].
    exists (S fuel).
    simpl.
      destruct (parseTableLookup s
                                 (peek (prefix ++ suffix)) tbl)
      as [gamma' |] eqn:Hlkp.
    * destruct (parseForest tbl gamma' (prefix ++ suffix) fuel)
        as (o, suffix') eqn:Hpf.
      destruct o as [f' |].
      -- rename s into x.
         assert (parseTableLookup x
                                  (peek (prefix ++ suffix))
                                  tbl =
                 Some gamma).
         { (* parseForest gamma and parseForest gamma' both
            succeed -- we should be able to prove that gamma
            and gamma' are the same *)
         apply parseForest_correct with (g := g) in H; auto.
         destruct H as [pre [Happ Hder]].
         assert (pre = prefix) by
             (apply prefixes_eq in Happ; auto).
         subst.
         pose proof Htbl as Htbl'.
         destruct Htbl as [Hmin Hcom].
         destruct prefix as [| ptok ptoks] eqn:Hpre; auto.

           - (* prefix is nil -- we have to look at the suffix 
                by decomposing it into prefix' and suffix' *)
             simpl in *.
             pose proof Hlkp as Hlkp'.
             apply lookup_exists in Hlkp.
             destruct Hlkp as [laMap [Hsf Hlf]].
             apply parseForest_correct with (g := g) in Hpf;
               auto.
             destruct Hpf as [prefix' [Happ' Hder']].
             unfold ptMinimal in Hmin.
             pose proof Hsf as Hsf2.
             destruct prefix' as [| ptok' ptoks'].
             
             + (* prefix' is nil *)
               destruct suffix' as [| stok' stoks'];
                 subst; simpl in *; auto.
               
               * (* prefix' and suffix' are nil -- x is 
                    nullable, and EOF is in FOLLOW(x) *)
                 apply Hmin with
                     (la := EOF)
                     (gamma := gamma') in Hsf; auto.
                 destruct Hsf as [Hfi | Hfo].
                 -- apply eof_fprod in Hfi; auto.
                    inv Hfi.
                 -- destruct Hfo as [Hnp Hfp].
                    inv Hfp.
                    assert (Hlkf : (@isLookaheadFor g) EOF x gamma).
                    { unfold isLookaheadFor.
                      right.
                      apply derivesForest_nil_nullable in Hder.
                      split; constructor; auto. }
                    apply Hcom in Hlkf.
                    destruct Hlkf as [laMap' [Hsf' Hlf']].
                    congruence.
                    
               * (* prefix' is nil, suffix' is cons -- stok' 
                    is in FOLLOW(x), but I'm not sure how to
                    handle the FIRST case *)
                 apply Hmin with (la := LA stok')
                                 (gamma := gamma') in Hsf; auto.
                 destruct Hsf as [Hfi | Hfo].
                 -- admit.
                 -- destruct Hfo as [Hnp Hfp].
                    inv Hfp.
                    assert (Hlkf : (@isLookaheadFor g) (LA stok') x gamma).
                    { unfold isLookaheadFor.
                      right.
                      apply derivesForest_nil_nullable in Hder.
                      split; constructor; auto. }
                    apply Hcom in Hlkf.
                    destruct Hlkf as [laMap' [Hsf' Hlf']].
                    congruence.
                    
             + (* prefix' is cons -- this violates the
                  Hmax hypothesis *)
               apply lookup_tbl_in_grammar
                 with (g := g) in Hlkp'; auto.
               assert ((@derivesTree g) (NT x)
                                          (ptok' :: ptoks')
                                          (Node x f')).
               { eapply derivesNT.
                 { apply Hlkp'. }
                 { auto. }}
               eapply Hmax in H; eauto.
                 simpl in H.
                 inv H.

           - (* prefix is ptok :: ptoks -- ptok is in 
                FIRST for (x, gamma) *)
             eapply derivesForest_cons_firstProd in Hder;
               eauto.
             assert ((@isLookaheadFor g) (LA ptok) x gamma) by
                 (unfold isLookaheadFor; auto).
             apply Hcom in H.
             destruct H as [laMap' [Hsf' Hlf']].
             simpl in *.
             assert (parseTableLookup x (LA ptok) tbl =
                     Some gamma).
             { unfold parseTableLookup.
               rewrite Hsf'.
               rewrite Hlf'.
               auto. }
             congruence. }

         congruence. (* Made it! *)

      -- (* This case should follow a similar pattern *)
        apply parseForest_correct with (g := g) in H; auto.
         destruct H as [pre [Happ Hder]].
         assert (pre = prefix) by admit.
         pose proof Hlkp as Hlkp'.
         apply lookup_exists in Hlkp.
         destruct Hlkp as [laMap [Hsf Hlf]].
         pose proof Htbl as Htbl'.
         unfold isParseTableFor in Htbl.
         destruct Htbl as [Hmin Hcom].
         apply parseForest_correct with (g := g) in Hpf; auto.
         destruct Hpf as [prefix' [Happ' Hder']].
         destruct prefix as [| ptok ptoks] eqn:Hpre.
         

             
           - eapply derivesForest_cons_firstProd in Hder;
               eauto.
             assert ((@isLookaheadFor g) (LA ptok) x gamma) by
                 (unfold isLookaheadFor; auto).
             apply Hcom in H.
             destruct H as [laMap' [Hsf' Hlf']].
             simpl in *.
             congruence. }
         congruence.

      -- 

         

           - auto.
           - 
         ++ (* prefix and suffix are nil *)
           apply derives_nil_nullable in Hder.
           unfold ptMinimal in Hmin.
           pose proof Hsf as Hsf1.
           apply Hmin with (gamma := gamma') (la := EOF) in Hsf.
           destruct Hsf as [Hfp | Hnp].
           ** apply eof_fprod in Hfp; inv Hfp; trivial.
           ** (* Now we know that (x, gamma') is nullable
                 and that EOF is in FOLLOW(x). We should be
                 able to prove that EOF is a lookahead symbol
                 for (x, gamma) *)
             destruct Hnp as [Hnp Hfp].
             inv Hfp.
             assert (Hlkf : (@isLookaheadFor g) EOF x gamma).
             { unfold isLookaheadFor.
               right; split.
               { constructor; auto. }
               { constructor; auto. }}
             apply Hcom in Hlkf.
             destruct Hlkf as [laMap' [Hsf' Hlf']].
             congruence.
           ** auto.
         ++ (* prefix is nil, suffix is (stok :: stoks) *)
           apply derives_nil_nullable in Hder.
           unfold ptMinimal in Hmin.
           pose proof Hsf as Hsf1.
           apply Hmin with (gamma := gamma') (la := LA stok)
             in Hsf.
           ** destruct Hsf as [Hfi | Hfo].
              --- (* stok in FIRST for (x, gamma'). 
                     This should mean that prefix' isn't empty.
                     prefix is empty, though -- that should
                     violate the Hmax hypothesis *)
                apply firstProd_not_nil with
                    (tbl := tbl)
                    (word := prefix')
                    (f := f') in Hfi; admit.
              ---admit.
           ** admit.
         ++ apply derives_cons_fprod
              with (x := x) in Hder; auto.
            assert ((@isLookaheadFor g) (LA ptok)
                                        x gamma).
            { unfold isLookaheadFor.
              left.
              auto. }
            unfold ptComplete in Hcom.
            apply Hcom in H.
            destruct H as [laMap' [Hsf' Hlf']].
            congruence.
                     
               













      
    * destruct (parseForest tbl gamma' (prefix ++ suffix)
                              fuel)
          as (o, suffix') eqn:Hpf.
        destruct o as [f' |].
      -- admit.
      -- 

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
