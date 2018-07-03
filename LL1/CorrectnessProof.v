Require Import List Omega String.
Require Import Derivation ExampleGrammars Grammar
               Lemmas LL1.Parser Tactics ParseTable
               ParseTree Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Lemma beqString_eq : 
  forall s s2,
    beqString s s2 = true
    -> s = s2.
Proof.
  intros; unfold beqString in H.
  destruct (StringMapFacts.eq_dec s s2); trivial.
  inv H.
Qed.

Lemma nt_derives_Node :
  forall tbl x input fuel tree suffix,
    parse tbl (NT x) input fuel = (Some tree, suffix) ->
    isNode tree = true.
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

Lemma t_derives_Leaf :
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

Lemma lookup_tbl_in_grammar : forall g x y tbl gamma,
    parse_table_for tbl g ->
    parseTableLookup x y tbl = Some gamma ->
    In (x, gamma) g.(productions).
Proof.
  intros.
  unfold parse_table_for in H. destruct H.
  unfold pt_minimal in H. 
  unfold pt_complete in H1.
  unfold parseTableLookup in H0.
  destruct (StringMap.find x tbl) eqn:Hnt.
  - destruct (LookaheadMap.find y t) eqn:Ht.
    + inv H0.
      apply H with
          (x := x)
          (la := y)
          (gamma := gamma)
          (laMap := t) in Hnt.
      * destruct Hnt.
        -- inv H0.
           auto.
        -- destruct H0.
           inv H0.
           auto.
      * auto.
    + inv H0.
  - inv H0.
Qed.

(*
      specialize H1 with
          (x := x)
          (tMap := t)
          (y := y)
          (gamma := gamma).
      apply H1 in Hnt. clear H1.
      * destruct Hnt.
        { inv H0. assumption. }
        destruct H0. inv H0.
        { assumption. }
      * assumption.
    + inv H0.
  - inv H0.
Qed.
*)

Theorem parse_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g ->
    forall (tr     : tree)
           (input  : list string)
           (sym    : symbol)
           (suffix : list string)
           (fuel   : nat),
      parse tbl sym input fuel = (Some tr, suffix) ->
    exists (prefix : list string),
      (prefix ++ suffix)%list = input /\
      (@derivesTree g) sym prefix tr.
Proof.
  intros g tbl Htbl tr.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_nested_ind with
      (P := fun tr =>
              forall input sym suffix fuel,
                parse tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr)
      (Q := fun subtrees =>
               forall input gamma suffix fuel,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees).

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
              apply IHparseForest in Hforest.
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
                apply derivesNil. }
              apply derivesNT with
                  (gamma := (hdRoot :: tlRoots)).
              { eapply lookup_tbl_in_grammar; eassumption. }
              { apply derivesCons; assumption. }}
            { inv Hparse. }}}
        { inv Hparse. }

  - intros input gamma suffix fuel HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * simpl in HparseForest. inv HparseForest.
        exists nil. split.
        { reflexivity. }
        apply derivesNil.
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
            apply IHparse in Htree.
            { destruct Htree as [treePrefix Htree].
              destruct Htree as [HappTree HderivesTree].
              apply IHparseForest in Hforest.
              destruct Hforest as [forestPrefix Hforest].
              destruct Hforest as [HappForest HderivesForest].
              subst.
              exists (treePrefix ++ forestPrefix)%list. split.
              { rewrite app_assoc. reflexivity. }
              apply derivesCons.
              { assumption. }
              assumption. }}
          inv HparseForest. }
        inv HparseForest.
Qed.
