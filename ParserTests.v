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

Definition E_tree :=
  Nd "E"
     (Fcons (Lf "num")
            (Fcons (Lf "==")
                   (Fcons (Lf "num")
                          Fnil))).

Definition S_print_tree :=
  Nd "S"
     (Fcons (Lf "print")
            (Fcons E_tree Fnil)).

Definition parseTree2 :=
  Nd "S"
     (Fcons (Lf "if")
            (Fcons E_tree
                   (Fcons (Lf "then")
                           (Fcons S_print_tree
                                  (Fcons (Lf "else")
                                         (Fcons S_print_tree
                                                Fnil)))))).



Example test1 :
  parse g311ParseTable "S" input1 100 = Accept parseTree1.
Proof. cbv. reflexivity. Defined.

(* The new definition works, too! *)
Example test2 :
  mkTree g311ParseTable (NT "S") input1 100 =
  (Some parseTree2, nil).
Proof. simpl. reflexivity. Defined.

Compute (mkTree g311ParseTable (NT "S") input1 100).