Require Import Grammar.
Require Import ParseTree.
Require Import List.
Require Import String.
Require Import Parser.
Import ListNotations.

Inductive derivesTree {g : grammar} : 
  symbol -> list string -> tree -> Prop :=
| derivesT : 
    forall (y : string),
      derivesTree (T y) [y] (Leaf y)
| derivesNT : 
    forall (x : string) 
           (gamma : list symbol) 
           (tokens : list string) 
           (subtrees : forest),
      In (NT x, gamma) g ->
      derivesForest gamma tokens subtrees ->
      derivesTree (NT x) tokens (Node x subtrees)
with derivesForest {g : grammar} : 
       list symbol -> list string -> forest -> Prop :=
     | derivesFnil : derivesForest [] [] Fnil
     | derivesFcons : 
         forall (hdRoot : symbol)
                (prefix suffix : list string)
                (hdTree : tree)
                (tlRoots : list symbol)
                (tlTrees : forest),
         derivesTree hdRoot prefix hdTree ->
         derivesForest tlRoots suffix tlTrees ->
         derivesForest (hdRoot :: tlRoots) 
                       (prefix ++ suffix) 
                       (Fcons hdTree tlTrees).