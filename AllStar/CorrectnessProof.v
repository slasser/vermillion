Require Import List String.
Require Import Lib.Derivation Lib.Grammar Lib.Lemmas
               Lib.ParseTree Lib.Tactics Lib.Utils.
Require Import AllStar.Parser AllStar.Subparser.
Import ListNotations.

Lemma nt_derives_Node :
  forall g x input stack fuel tree suffix,
    parse' g (NT x) input stack fuel = (Some tree, suffix) ->
    isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct (adaptivePredict g x input stack).
    + destruct (parseForest g l input stack fuel).
      destruct o.
      * inv H. reflexivity.
      * inv H.
    + inv H.
    + inv H.
Qed.

Lemma t_derives_Leaf :
  forall g y input stack fuel tree suffix,
    parse' g (T y) input stack fuel = (Some tree, suffix) ->
    isLeaf tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (beqSym (T y) (T s)).
      * inv H. reflexivity.
      * inv H.
Qed.

Axiom silly_in_grammar : forall (g : grammar) x ys,
    In (x, ys) g.

Theorem parse'_correct :
  forall (g      : grammar)
         (tr     : tree)
         (sym    : symbol)
         (input  : list string)
         (stack  : list symbol)
         (fuel   : nat)
         (suffix : list string),
    parse' g sym input stack fuel = (Some tr, suffix) ->
    exists (prefix : list string),
      (prefix ++ suffix)%list = input /\
      (@derivesTree g) sym prefix tr.
Proof.
  intros g tr.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_mutual_ind with
      (P := fun tr =>
              forall sym input stack fuel suffix,
                parse' g sym input stack fuel =
                (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr)
      (P0 := fun subtrees =>
               forall gamma input stack fuel suffix,
                 parseForest g gamma input stack fuel =
                 (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees).
  - intros sym input stack fuel suffix Hparse'.
    destruct fuel as [| fuel].
    + inv Hparse'.
    + destruct sym as [y | x].
      * destruct input as [| token input].
        { inv Hparse'. }
        simpl in Hparse'.
        destruct (beqSym (T y) (T token)) eqn:Hbeq.
        { inv Hparse'. exists [token]. split.
          { reflexivity. }
          apply eq_sym_eq_T in Hbeq. subst. apply derivesT. }
        inv Hparse'.
      * apply nt_derives_Node in Hparse'. inv Hparse'.
  - (* 2nd case *)
    intros sym input stack fuel suffix Hparse'.
    destruct fuel as [| fuel].
    + inv Hparse'.
    + destruct sym as [y | x].
      * apply t_derives_Leaf in Hparse'. inv Hparse'.
      * simpl in Hparse'.
        destruct (adaptivePredict g x input stack)
                 as [ys | sps | ] eqn:Hpred.
        { destruct (parseForest g ys input stack fuel)
            as [subresult input'] eqn:Hforest.
          destruct subresult as [subtrees |].
          { inv Hparse'. apply IHparseForest in Hforest.
            clear IHparseForest.
            destruct Hforest as [prefix Hforest].
            exists prefix.
            destruct Hforest as [Happ Hderives]. split.
            { assumption. }
            inv Hderives.
            { apply derivesNT with (gamma := nil).
              { (* Here's where we need a lemma saying that
                   whenever adaptivePredict returns Choice ys,
                   ys is in the grammar. *)
                apply silly_in_grammar. }
              apply derivesFnil. }
            eapply derivesNT.
            { apply silly_in_grammar. }
            eapply derivesFcons.
            { eassumption. }
            eassumption. }
          inv Hparse'. }
        { inv Hparse'. }
        inv Hparse'.
Abort.

(* stuff copied from the LL(1) correctness proof
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
Defined.
*)