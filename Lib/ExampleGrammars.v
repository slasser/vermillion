Require Import List String.
Require Import Grammar ParseTable ParseTree.
Import ListNotations.
Open Scope string_scope.

(* Grammar 3.11 from "Modern Compiler Implementation in ML" *)
Definition g311 : grammar :=
{| productions :=
     [("S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]);
      ("S", [T "begin"; NT "S"; NT "L"]);
      ("S", [T "print"; NT "E"]);
        
      ("L", [T "end"]);
      ("L", [T ";"; NT "S"; NT "L"]);
        
      ("E", [T "num"; T "=="; T "num"])];
   start := "S" |}.
     
(* Grammar 3.11 parse table definitions *)

Definition S_map :=
  LookaheadMap.add
    (LA "if")
    [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]
    (LookaheadMap.add
       (LA "begin")
       [T "begin"; NT "S"; NT "L"]
       (LookaheadMap.add
          (LA "print")
          [T "print"; NT "E"]
          (LookaheadMap.empty (list symbol)))).

Definition L_map :=
  LookaheadMap.add
    (LA "end")
    [T "end"]
    (LookaheadMap.add
       (LA ";")
       [T ";"; NT "S"; NT "L"]
       (LookaheadMap.empty (list symbol))).

Definition E_map :=
  LookaheadMap.add
    (LA "num")
    [T "num"; T "=="; T "num"]
    (LookaheadMap.empty (list symbol)).

Definition g311ParseTable :=
  StringMap.add
    "S" S_map
    (StringMap.add
       "L" L_map
       (StringMap.add
          "E" E_map
          (StringMap.empty (LookaheadMap.t (list symbol))))).

(* For testing purposes, a valid sentence in L(g311) 
   and its derivation tree *)

Definition g311Sentence1 :=
  ["if"; "num"; "=="; "num"; "then";
     "print"; "num"; "=="; "num";
    "else";
     "print"; "num"; "=="; "num"].

Definition E_tree := Node "E" [Leaf "num"; Leaf "=="; Leaf "num"].

Definition S_print_tree := Node "S" [Leaf "print"; E_tree].

Definition g311ParseTree1 :=
  Node "S" [Leaf "if"; E_tree; Leaf "then";
              S_print_tree;
            Leaf "else";
              S_print_tree].

(* Grammar 3.12 from the same textbook *)

Definition g312 : grammar :=
  {| productions :=
       [("Z", [T "d"]); 
        ("Z", [NT "X"; NT "Y"; NT "Z"]);
        ("Y", []);
        ("Y", [T "c"]);
        ("X", [NT "Y"]);
        ("X", [T "a"])];
     start := "Z" |}.
