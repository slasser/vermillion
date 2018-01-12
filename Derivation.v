Require Import Grammar.
Require Import ParseTree.
Require Import List.
Require Import String.
Require Import Parser.
Import ListNotations.

Inductive derives {g : grammar} : symbol -> list string -> parse_tree -> Prop :=
| derivesT  : forall (tName : string),
    derives (T tName)  [tName] (Leaf tName)
| derivesNT : forall (ntName : string) (prod : production) (tokens : list string) (subtrees : list parse_tree),
    In prod g /\ derivesList (rhs prod) tokens subtrees /\ lhs prod = (NT ntName) ->
    derives (NT ntName) tokens (Node ntName subtrees)

with derivesList {g : grammar} : list symbol -> list string -> list parse_tree -> Prop :=
     | derivesNil  : derivesList nil nil nil
     | derivesCons :
         forall (hdRoot : symbol) (prefix : list string) (hdSubtree : parse_tree),                  
           derives hdRoot prefix hdSubtree ->
           
           forall (tlRoots : list symbol) (suffix : list string) (tlSubtrees : list parse_tree),
             derivesList tlRoots suffix tlSubtrees ->
             
             derivesList (hdRoot :: tlRoots) (prefix ++ suffix) (hdSubtree :: tlSubtrees).


(* Binary version of the derives relation *)
Inductive derives2 {g : grammar} : symbol -> list string -> Prop :=
| derivesT2  : forall (tName : string),
    derives2 (T tName)  [tName]
| derivesNT2 : forall (ntName : string) (prod : production) (tokens : list string),
    In prod g /\ derivesList2 (rhs prod) tokens /\ lhs prod = (NT ntName) ->
    derives2 (NT ntName) tokens
            
with derivesList2 {g : grammar} : list symbol -> list string -> Prop :=
     | derivesNil2  : derivesList2 nil nil
     | derivesCons2 :
         forall (hdRoot : symbol) (prefix : list string),
           derives2 hdRoot prefix ->
           
           forall (tlRoots : list symbol) (suffix : list string),
             derivesList2 tlRoots suffix ->
             derivesList2 (hdRoot :: tlRoots) (prefix ++ suffix).