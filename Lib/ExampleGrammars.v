Require Import List String.
Require Import Grammar ParseTable ParseTree.
Import ListNotations.
Open Scope string_scope.

(* Named nonterminal constants for convenience. *)
Definition X := 0.
Definition L := 1.
Definition E := 2.
Definition Y := 3.
Definition Z := 4.

(* Grammar 3.11 from "Modern Compiler Implementation in ML" *)
Definition g311 : grammar :=
{| productions :=
     [(X, [T "if"; NT E; T "then"; NT X; T "else"; NT X]);
      (X, [T "begin"; NT X; NT L]);
      (X, [T "print"; NT E]);
        
      (L, [T "end"]);
      (L, [T ";"; NT X; NT L]);
        
      (E, [T "num"; T "=="; T "num"])];
   start := X |}.
     
(* Grammar 3.11 parse table definitions *)

Definition X_map :=
  LaMap.add
    (LA "if")
    [T "if"; NT E; T "then"; NT X; T "else"; NT X]
    (LaMap.add
       (LA "begin")
       [T "begin"; NT X; NT L]
       (LaMap.add
          (LA "print")
          [T "print"; NT E]
          (LaMap.empty (list symbol)))).

Definition L_map :=
  LaMap.add
    (LA "end")
    [T "end"]
    (LaMap.add
       (LA ";")
       [T ";"; NT X; NT L]
       (LaMap.empty (list symbol))).

Definition E_map :=
  LaMap.add
    (LA "num")
    [T "num"; T "=="; T "num"]
    (LaMap.empty (list symbol)).

Definition g311ParseTable :=
  NtMap.add
    X X_map
    (NtMap.add
       L L_map
       (NtMap.add
          E E_map
          (NtMap.empty (LaMap.t (list symbol))))).

(* For testing purposes, a valid sentence in L(g311) 
   and its derivation tree *)

Definition g311Sentence1 :=
  ["if"; "num"; "=="; "num"; "then";
     "print"; "num"; "=="; "num";
    "else";
     "print"; "num"; "=="; "num"].

Definition E_tree := Node E [Leaf "num"; Leaf "=="; Leaf "num"].

Definition X_print_tree := Node X [Leaf "print"; E_tree].

Definition g311ParseTree1 :=
  Node X [Leaf "if"; E_tree; Leaf "then";
              X_print_tree;
            Leaf "else";
              X_print_tree].

(* Grammar 3.12 from the same textbook *)

Definition g312 : grammar :=
  {| productions :=
       [(Z, [T "d"]); 
        (Z, [NT X; NT Y; NT Z]);
        (Y, []);
        (Y, [T "c"]);
        (X, [NT Y]);
        (X, [T "a"])];
     start := Z |}.

