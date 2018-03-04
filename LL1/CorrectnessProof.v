Require Import List Omega String.
Require Import Derivation ExampleGrammars Grammar
               Lemmas LL1.Parser Tactics ParseTable
               ParseTree Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.

Lemma nt_derives_Node :
  forall tbl x input fuel tree suffix,
    parse tbl (NT x) input fuel = (Some tree, suffix) ->
    isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (parseTableLookup (NT x) (T s) tbl).
      * destruct (parseForest tbl l (s :: input) fuel) in H.
        destruct o.
        { inv H. simpl. reflexivity. }
        inv H.
      * inv H.
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
    + destruct (beqSym (T y) (T s)).
      * inv H. reflexivity.
      * inv H.
Qed.

Lemma lookup_tbl_in_grammar : forall g x y tbl gamma,
    isParseTableFor tbl g ->
    parseTableLookup (NT x) (T y) tbl = Some gamma ->
    In (NT x, gamma) g.
Proof.
  intros.
  unfold isParseTableFor in H. destruct H.
  unfold parseTableComplete in H. destruct H.
  unfold parseTableMinimal in H1.
  unfold parseTableLookup in H0.
  destruct (SymbolMap.find (NT x) tbl) eqn:Hnt.
  - destruct (SymbolMap.find (T y) t) eqn:Ht.
    + inv H0.
      specialize H1 with
          (x := NT x)
          (tMap := t)
          (y := T y)
          (gamma := gamma).
      apply H1 in Hnt. clear H1.
      * destruct Hnt.
        { inv H0. assumption. }
        destruct H0. inv H0.
        { assumption. }
      * assumption.
    + inv H0.
  - inv H0.
Defined.


Theorem parse_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g ->
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
      using tree_mutual_ind with
      (P := fun tr =>
              forall input sym suffix fuel,
                parse tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr)
      (P0 := fun subtrees =>
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
        destruct (beqSym (T y) (T token)) eqn:Hbeq.
        { inv Hparse. exists [token]. split.
          { reflexivity. }
          apply eq_sym_eq_T in Hbeq. subst.
          apply derivesT. }
        inv Hparse.
      * apply nt_derives_Node in Hparse. inv Hparse.
  - intros input sym suffix fuel Hparse.
    destruct fuel as [| fuel].
    + inv Hparse.
    + destruct sym as [y | x].
      * apply t_derives_Leaf in Hparse. inv Hparse.
      * destruct input as [| token input].
        { inv Hparse. }
        simpl in Hparse.
        destruct (parseTableLookup (NT x) (T token) tbl)
                 as [ys |] eqn:Hlookup.
        { destruct (parseForest tbl ys (token :: input) fuel)
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
                { apply lookup_tbl_in_grammar with
                      (g := g)
                      (x := s)
                      (y := token)
                      (gamma:=nil) in Hlookup.
                  { assumption. }
                  assumption. }
                apply derivesFnil. }
              apply derivesNT with
                  (gamma := (hdRoot :: tlRoots)).
              { apply lookup_tbl_in_grammar
                  with (g := g)
                       (x:=s)
                       (y:= token)
                       (gamma:=hdRoot::tlRoots) in Htbl;
                  assumption. }
              apply derivesFcons.
              { assumption. }
              assumption. }
            inv Hparse. }}
        inv Hparse.
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
            apply IHparse in Htree.
            { destruct Htree as [treePrefix Htree].
              destruct Htree as [HappTree HderivesTree].
              apply IHparseForest in Hforest.
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

