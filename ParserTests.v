Require Import Grammar.
Require Import ExampleGrammars.
Require Import List.
Require Import Parser.
Require Import ParseTree.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Example test1 :
  mkTree g311ParseTable (NT "S") g311Sentence1 100 =
  (Some g311ParseTree1, nil).
Proof. simpl. reflexivity. Defined.