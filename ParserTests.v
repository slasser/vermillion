Require Import GrammarSymbol.
Require Import Grammar.
Require Import ExampleGrammars.
Require Import List.
Require Import Parser.
Require Import ParseTree.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition input1 := ["if"; "num"; "=="; "num"; "then"; "print"; "num"; "=="; "num"; "else"; "print"; "num"; "=="; "num"].
Definition pt1 := Node "S" [Leaf "if";
                            Node "E" [Leaf "num"; Leaf "=="; Leaf "num"];
                            Leaf "then";
                            Node "S" [Leaf "print";
                                      Node "E" [Leaf "num"; Leaf "=="; Leaf "num"]];
                            Leaf "else";
                            Node "S" [Leaf "print";
                                      Node "E" [Leaf "num"; Leaf "=="; Leaf "num"]]].

Example test1 :
  parse (mkParseTable g311 100) (NT "S") input1 100 =
  Some (pt1, []).
Proof. simpl. reflexivity. Defined.

(* Test of the stack-based parse function. *)
Example test1' : parse' (mkParseTable g311 100) (NT "S") input1 100 = true.
Proof. cbv. reflexivity. Defined.