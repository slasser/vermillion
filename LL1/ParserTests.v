Require Import List.

Require Import Lib.ExampleGrammars.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.

Require Import LL1.Parser.
Require Import LL1.ParseTable.

Import ListNotations.

Example test1 :
  parse g311ParseTable (NT X) g311Sentence1 100 =
  (Some g311ParseTree1, nil).
Proof. simpl. reflexivity. Qed.

Definition x_y_grammar :=
  [(NT X, [NT Y]);
     (NT Y, [])].

Definition x_map := 
  LaMap.add 
    EOF [NT Y]
    (LaMap.empty (list symbol)).

Definition y_map := 
  LaMap.add 
    EOF nil
    (LaMap.empty (list symbol)).

Definition x_y_parse_table :=
  NtMap.add
    X x_map
    (NtMap.add
       Y y_map
       (NtMap.empty (LaMap.t (list symbol)))).
                
Example x_y_test1 :
  parse x_y_parse_table (NT X) nil 100 =
  (Some (Node X [Node Y []]), nil).
Proof. auto. Qed.

