Require Import Derivation.
Require Import ExampleGrammars.
Require Import Grammar.
Require Import Lemmas.
Require Import List.
Require Import Parser.
Require Import ParserTactics.
Require Import ParseTable.
Require Import ParseTableTests.
Require Import ParseTree.
Require Import String.
Require Import Omega.
Require Import ParserUtils.
Import ListNotations.
Open Scope list_scope.
Open Scope string_scope.
  
Lemma terminal_step :
  forall (tbl   : parse_table)
         (tName : string)
         (token : string)
         (gramStack' : list stack_elt)
         (semStack  : list parse_tree)
         (input : list string)
         (tree : parse_tree)
         (fuel  : nat),
    cmpSymbol (T tName) (T token) = true ->
    parseLoop tbl
              (Sym (T tName) :: gramStack')
              semStack
              (token :: input)
              (S fuel) = Accept tree
    <->
    parseLoop tbl
              gramStack'
              (Leaf tName :: semStack)
              input
              fuel = Accept tree.
Proof.
  split.
  - intros. simpl in H0.  rewrite H in H0. assumption.
  - intros. simpl. rewrite H. assumption.
Defined.

Lemma nonterminal_step :
  forall (tbl   : parse_table)
         (ntName : string)
         (gamma : list symbol)
         (gramStack' : list stack_elt)
         (syms : list stack_elt)
         (gammaLength : nat)
         (semStack  : list parse_tree)
         (token : string)
         (input : list string)
         (tree : parse_tree)
         (fuel  : nat),
    parseTableLookup (NT ntName) (T token) tbl = Some gamma ->
    syms = map Sym gamma ->
    gammaLength = List.length gamma ->
    parseLoop tbl
              (Sym (NT ntName) :: gramStack')
              semStack
              (token :: input)
              (S fuel) = Accept tree
    <->
    parseLoop tbl
              (syms ++ Sep ntName gammaLength :: gramStack')
              semStack
              (token :: input)
              fuel = Accept tree.
Proof.
  split.
  - intros. simpl in H2.
    rewrite H in H2. rewrite <- H0 in H2.
    rewrite <- H1 in H2. assumption.
  - intros. simpl.
    rewrite H. rewrite <- H0.
    rewrite <- H1. assumption.
Defined.

Lemma derives_singleton_list_of_NT_implies_derives_NT :
  forall (g : grammar)
         (ntName : string)
         (tokens : list string),
    (@derivesList2 g) [NT ntName] tokens ->
    (@derives2 g) (NT ntName) tokens.
Proof.
  intros. inv H. inv H4.
  rewrite app_nil_r. assumption.
Defined.

(* Come back to this *)
Lemma ptLookup_In :
  forall tbl g x y ys,
    isParseTableFor tbl g ->
    parseTableLookup x y tbl = Some ys ->
    In (x, ys) g.
Proof.
  intros tbl g x y ys Htbl Hlookup.
  destruct Htbl as [Hcomplete Hminimal].
  unfold parseTableMinimal in Hminimal.
  unfold parseTableLookup in Hlookup.
Abort.

Lemma eq_sym_eq_T : forall s s2,
    cmpSymbol (T s) (T s2) = true <->
    s = s2.
Proof.
  split.
  - intros. unfold cmpSymbol in H.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2)).
    + inv e. reflexivity.
    + inv H.
  - intros. unfold cmpSymbol.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2)).
    + reflexivity.
    + exfalso. apply n. subst. reflexivity.
Defined.

Print tree_ind'.

Definition isNd tr :=
  match tr with
  | Lf _ => false
  | Nd _ _ => true
  end.

Lemma nt_derives_node :
  forall tbl x input fuel tree suffix,
    mkTree tbl (NT x) input fuel = (Some tree, suffix) ->
    isNd tree = true.
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

Definition isLf tr := negb (isNd tr).

Lemma t_derives_Leaf :
  forall tbl y input fuel tree suffix,
    mkTree tbl (T y) input fuel = (Some tree, suffix) ->
    isLf tree = true.
Proof.
  intros. destruct fuel.
  - inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (cmpSymbol (T y) (T s)).
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
      (@derTree g) sym prefix tr.
Proof.
  intros.
  generalize dependent sym.
  generalize dependent input.
  generalize dependent suffix.
  generalize dependent fuel. 
  induction tr using tree_ind' with
      (P := fun tr =>
              forall fuel suffix input sym,
                mkTree tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derTree g) sym prefix tr)
      (P0 := fun subtrees =>
               forall fuel suffix input gamma,
                 mkForest tbl gamma input fuel = (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derForest g) gamma prefix subtrees).
  - intros. destruct fuel.
    + inv H0.
    + destruct sym.
      * destruct input.
        { inv H0. }
        simpl in H0.
        destruct (cmpSymbol (T s0) (T s1)) eqn:Hcmp.
        { inv H0. exists [s1]. split.
          { reflexivity. }
          apply eq_sym_eq_T in Hcmp. subst.
          apply derT. }
        inv H0.
      * apply nt_derives_node in H0. inv H0.
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
              { apply derNT with (gamma := nil).
                { apply lookup_tbl_in_grammar with (g := g)
                    in Htbl.
                  { assumption. }
                  assumption. }
                apply derFnil. }
              apply derNT with (gamma := (hdRoot :: tlRoots)).
              { apply lookup_tbl_in_grammar with (g := g)
                  in Htbl; assumption. }
              apply derFcons.
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
        apply derFnil.
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
            apply derFcons.
            { assumption. }
            assumption. }
          inv H0. }
        inv H0.
Defined.