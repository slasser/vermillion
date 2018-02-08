Require Import Derivation.
Require Import ExampleGrammars.
Require Import Grammar.
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

Lemma nt_derives_node :
  forall tbl x input fuel tree suffix,
    mkTree tbl (NT x) input fuel = (Some tree, suffix) ->
    isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (parseTableLookup (NT x) (T s) tbl).
      * destruct (mkSubtrees tbl l (s :: input) [] fuel) in H.
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
    + destruct (cmpSymbol (T y) (T s)).
      * inv H. reflexivity.
      * inv H.
Defined.

Lemma mkSubtreesCorrect :
  forall (g     : grammar)
         (tbl   : parse_table)
         (gamma : list symbol)
         (input : list string)
         (fuel  : nat)
         (acc   : list (@parse_tree string))
         (subtrees  : list parse_tree)
         (suffix : list string),
    isParseTableFor tbl g -> 
    mkSubtrees tbl gamma input acc fuel =
    (Some subtrees, suffix) ->
    exists prefix,
      (prefix ++ suffix)%list = input /\
      (@derivesList g) gamma prefix subtrees.
Proof. Abort.  

Lemma parserCorrect :
  forall (g     : grammar)
         (tbl   : parse_table)
         (start : symbol)
         (input : list string)
         (fuel  : nat)
         (tree  : parse_tree)
         (suffix : list string),
    isParseTableFor tbl g -> 
    mkTree tbl start input fuel = (Some tree, suffix) ->
    exists prefix,
      (prefix ++ suffix)%list = input /\
      (@derives g) start prefix tree.
Proof.
Admitted.