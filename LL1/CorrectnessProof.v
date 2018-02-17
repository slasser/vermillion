Require Import List Omega String.
Require Import Derivation ExampleGrammars Grammar
               Lemmas Parser Tactics ParseTable
               ParseTree Utils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
  
Lemma eq_sym_eq_T : 
  forall (s s2 : string),
    beqSym (T s) (T s2) = true <-> s = s2.
Proof.
  split; intro H.
  - unfold beqSym in H.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2)) as [Heq | Hneq].
    + inv Heq; reflexivity.
    + inv H.
  - unfold beqSym.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2)) as [Heq | Hneq].
    + reflexivity.
    + exfalso. apply Hneq. subst. reflexivity.
Defined.

Lemma nt_derives_Node :
  forall tbl x input fuel tree suffix,
    mkTree tbl (NT x) input fuel = (Some tree, suffix) ->
    isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (parseTableLookup (NT x) (T s) tbl).
      * destruct (mkForest tbl l (s :: input) fuel) in H.
        destruct o.
        { inv H. simpl. reflexivity. }
        inv H.
      * inv H.
Defined.

Lemma t_derives_Leaf :
  forall tbl y input fuel tree suffix,
    mkTree tbl (T y) input fuel = (Some tree, suffix) ->
    isLeaf tree = true.
Proof.
  intros. destruct fuel.
  - inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (beqSym (T y) (T s)).
      * inv H. reflexivity.
      * inv H.
Defined.

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


Theorem parse_correct : forall tbl g sym input tr suffix fuel,
    isParseTableFor tbl g ->
    mkTree tbl sym input fuel = (Some tr, suffix) ->
    exists prefix,
      (prefix ++ suffix)%list = input /\
      (@derivesTree g) sym prefix tr.
Proof.
  intros.
  generalize dependent sym.
  generalize dependent input.
  generalize dependent suffix.
  generalize dependent fuel. 
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall fuel suffix input sym,
                mkTree tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr)
      (P0 := fun subtrees =>
               forall fuel suffix input gamma,
                 mkForest tbl gamma input fuel = (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees).
  - intros. destruct fuel.
    + inv H0.
    + destruct sym.
      * destruct input.
        { inv H0. }
        simpl in H0.
        destruct (beqSym (T s0) (T s1)) eqn:Hcmp.
        { inv H0. exists [s1]. split.
          { reflexivity. }
          apply eq_sym_eq_T in Hcmp. subst.
          apply derivesT. }
        inv H0.
      * apply nt_derives_Node in H0. inv H0.
  - intros. destruct fuel.
    + inv H0.
    + destruct sym.
      * apply t_derives_Leaf in H0. inv H0.
      * destruct input.
        { inv H0. }
        simpl in H0.
        destruct (parseTableLookup (NT s0) (T s1) tbl) eqn:Htbl.
        { destruct (mkForest tbl l (s1 :: input) fuel)
                   eqn:Hforest.
          { destruct o.
            { inv H0.
              apply IHtr in Hforest.
              destruct Hforest.
              exists x. destruct H0. split.
              { assumption. }
              inv H1.
              { apply derivesNT with (gamma := nil).
                { apply lookup_tbl_in_grammar with (g := g)
                    in Htbl.
                  { assumption. }
                  assumption. }
                apply derivesFnil. }
              apply derivesNT with (gamma := (hdRoot :: tlRoots)).
              { apply lookup_tbl_in_grammar with (g := g)
                  in Htbl; assumption. }
              apply derivesFcons.
              { assumption. }
              assumption. }
            inv H0. }}
        inv H0.
  - intros. simpl in H0. destruct fuel.
    + inv H0.
    + destruct gamma.
      * simpl in H0. inv H0.
        exists nil. split.
        { reflexivity. }
        apply derivesFnil.
      * exfalso.
        simpl in H0.
        destruct (mkTree tbl s input fuel).
        destruct o.
        { destruct (mkForest tbl gamma l fuel).
          destruct o.
          { inv H0. }
          inv H0. }
        inv H0.
  - intros. destruct fuel.
    + inv H0.
    + destruct gamma.
      * inv H0.
      * simpl in H0. destruct (mkTree tbl s input fuel) eqn:Htree.
        destruct o.
        { destruct (mkForest tbl gamma l fuel) eqn:Hforest.
          destruct o.
          { inv H0.
            apply IHtr in Htree. destruct Htree. destruct H0.
            apply IHtr0 in Hforest. destruct Hforest.
            destruct H2. subst.
            exists (x ++ x0)%list. split.
            { rewrite app_assoc. reflexivity. }
            apply derivesFcons.
            { assumption. }
            assumption. }
          inv H0. }
        inv H0.
Defined.

