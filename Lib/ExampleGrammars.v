Require Import List String.
Require Import Grammar ParseTable ParseTree.
Import ListNotations.
Open Scope string_scope.

(* Named nonterminal constants for convenience. *)
Definition S := 0.
Definition E := 1.
Definition L := 2.

(* Grammar 3.11 from "Modern Compiler Implementation in ML" *)
Definition g311 : grammar :=
{| productions :=
     [(S, [T "if"; NT E; T "then"; NT S; T "else"; NT S]);
      (S, [T "begin"; NT S; NT L]);
      (S, [T "print"; NT E]);
        
      (L, [T "end"]);
      (L, [T ";"; NT S; NT L]);
        
      (E, [T "num"; T "=="; T "num"])];
   start := S |}.
     
(* Grammar 3.11 parse table definitions *)

Definition S_map :=
  LaMap.add
    (LA "if")
    [T "if"; NT E; T "then"; NT S; T "else"; NT S]
    (LaMap.add
       (LA "begin")
       [T "begin"; NT S; NT L]
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
       [T ";"; NT S; NT L]
       (LaMap.empty (list symbol))).

Definition E_map :=
  LaMap.add
    (LA "num")
    [T "num"; T "=="; T "num"]
    (LaMap.empty (list symbol)).

Definition g311ParseTable :=
  NtMap.add
    S S_map
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

Definition S_print_tree := Node S [Leaf "print"; E_tree].

Definition g311ParseTree1 :=
  Node S [Leaf "if"; E_tree; Leaf "then";
              S_print_tree;
            Leaf "else";
              S_print_tree].

(* Grammar 3.12 from the same textbook *)

Definition X := 3.
Definition Y := 4.
Definition Z := 5.

Definition g312 : grammar :=
  {| productions :=
       [(Z, [T "d"]); 
        (Z, [NT X; NT Y; NT Z]);
        (Y, []);
        (Y, [T "c"]);
        (X, [NT Y]);
        (X, [T "a"])];
     start := Z |}.

