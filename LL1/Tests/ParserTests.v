Require Import List.

Require Import Lib.ExampleGrammars.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.

Require Import LL1.Parser.
Require Import LL1.ParseTable.
Require Import LL1.Tests.ExampleParseTables.

Import ListNotations.

Example g311_test :
  parse g311ParseTable (NT X) g311Sentence1 100 =
  (Some g311ParseTree1, nil).
Proof. auto. Qed.
                
Example xy_test :
  parse xy_parse_table (NT X) nil 100 =
  (Some (Node X [Node Y []]), nil).
Proof. auto. Qed.

