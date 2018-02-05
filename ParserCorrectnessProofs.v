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


Lemma parserCorrect :
  forall (g     : grammar)
         (tbl   : parse_table)
         (start : string)
         (input : list string)
         (fuel  : nat)
         (tree  : parse_tree),
    isParseTableFor tbl g -> 
    parse tbl start input fuel = Accept tree ->
    exists prefix suffix,
      (prefix ++ suffix)%list = input /\
      (@derives g) (NT start) prefix tree.
Proof.
  intros. destruct fuel.
  - unfold parse in H0. simpl in H0. inv H0.
  - induction tree.
    + unfold parse in H0. simpl in H0.
Abort.