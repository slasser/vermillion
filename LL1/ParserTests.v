Require Import List String.
Require Import ExampleGrammars Grammar Parser ParseTree.
Import ListNotations.
Open Scope string_scope.

Example test1 :
  mkTree g311ParseTable (NT "S") g311Sentence1 100 =
  (Some g311ParseTree1, nil).
Proof. simpl. reflexivity. Defined.

