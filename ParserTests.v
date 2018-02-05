Require Import Grammar.
Require Import ExampleGrammars.
Require Import List.
Require Import Parser.
Require Import ParseTree.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition input1 :=
  ["if"; "num"; "=="; "num"; "then";
     "print"; "num"; "=="; "num";
    "else";
      "print"; "num"; "=="; "num"].
Definition parseTree1 :=
  Node "S"
       [Leaf "if";
        Node "E"
             [Leaf "num"; Leaf "=="; Leaf "num"];
        Leaf "then";
        Node "S"
             [Leaf "print";
              Node "E"
                   [Leaf "num"; Leaf "=="; Leaf "num"]];
        Leaf "else";
        Node "S"
             [Leaf "print";
              Node "E"
                   [Leaf "num"; Leaf "=="; Leaf "num"]]].

Example test1 :
  parse g311ParseTable "S" input1 100 = Accept parseTree1.
Proof. cbv. reflexivity. Defined.