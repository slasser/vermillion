Require Import List String.
Require Import Grammar ParseTree.
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
      In (x, gamma) g.(productions) ->
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

Definition derivesMaximalTree (g : grammar)
           (sym : symbol) (pre suf : list string)
           (tree : tree) :=
    (@derivesTree g) sym pre tree
    /\ forall pre' suf' tree',
      (pre ++ suf)%list = (pre' ++ suf')%list
        -> (@derivesTree g) sym pre' tree'
        -> span tree' <= span tree.

Definition derivesMaximalForest (g : grammar)
           (x : nonterminal) (gamma : list symbol)
           (pre suf : list string)
           (f : forest) :=
  In (x, gamma) (productions g)
  /\ (@derivesForest g) gamma pre f
  /\ forall gamma' pre' suf' f',
      In (x, gamma') (productions g)
      -> (pre ++ suf)%list = (pre' ++ suf')%list
      -> (@derivesForest g) gamma' pre' f'
      -> spanForest f' <= spanForest f.
