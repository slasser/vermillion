Require Import Grammar ParseTree.
Require Import List String.
Import ListNotations.
Open Scope string_scope.

(* Grammar 3.11 from "Modern Compiler Implementation in ML" *)
Definition g311 : grammar :=
  [(NT "S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]);
   (NT "S", [T "begin"; NT "S"; NT "L"]);
   (NT "S", [T "print"; NT "E"]);
  
   (NT "L", [T "end"]);
   (NT "L", [T ";"; NT "S"; NT "L"]);
   
   (NT "E", [T "num"; T "=="; T "num"])].

(* Grammar 3.11 parse table definitions *)

Definition S_map :=
  SymbolMap.add
    (T "if")
    [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]
    (SymbolMap.add
       (T "begin")
       [T "begin"; NT "S"; NT "L"]
       (SymbolMap.add
          (T "print")
          [T "print"; NT "E"]
          (SymbolMap.empty (list symbol)))).

Definition L_map :=
  SymbolMap.add
    (T "end")
    [T "end"]
    (SymbolMap.add
       (T ";")
       [T ";"; NT "S"; NT "L"]
       (SymbolMap.empty (list symbol))).

Definition E_map :=
  SymbolMap.add
    (T "num")
    [T "num"; T "=="; T "num"]
    (SymbolMap.empty (list symbol)).

Definition g311ParseTable :=
  SymbolMap.add
    (NT "S") S_map
    (SymbolMap.add
       (NT "L") L_map
       (SymbolMap.add
          (NT "E") E_map
          (SymbolMap.empty (SymbolMap.t (list symbol))))).

(* For testing purposes, a valid sentence in L(g311) 
   and its derivation tree *)

Definition g311Sentence1 :=
  ["if"; "num"; "=="; "num"; "then";
     "print"; "num"; "=="; "num";
    "else";
      "print"; "num"; "=="; "num"].

Definition E_tree :=
  Node "E"
     (Fcons (Leaf "num")
            (Fcons (Leaf "==")
                   (Fcons (Leaf "num")
                          Fnil))).

Definition S_print_tree :=
  Node "S"
     (Fcons (Leaf "print")
            (Fcons E_tree Fnil)).

Definition g311ParseTree1 :=
  Node "S"
     (Fcons (Leaf "if")
            (Fcons E_tree
                   (Fcons (Leaf "then")
                           (Fcons S_print_tree
                                  (Fcons (Leaf "else")
                                         (Fcons S_print_tree
                                                Fnil)))))).

(* Grammar 3.12 from the same textbook *)

Definition g312 : grammar :=
  [(NT "Z", [T "d"]); 
   (NT "Z", [NT "X"; NT "Y"; NT "Z"]);
   (NT "Y", []);
   (NT "Y", [T "c"]);
   (NT "X", [NT "Y"]);
   (NT "X", [T "a"])].