Require Import List.
Require Import String.
Require Import Parser.
Import ListNotations.

(* To do : rephrase this in terms of a grammar and it's productions.
   At the moment, NT and subtrees in derivesNT could be from different productions. *)

Inductive derives {g : grammar} : symbol -> list string -> ast -> Prop :=
| derivesT  : forall (tName : string),
    derives (T tName)  [tName] (Leaf tName)
| derivesNT : forall (ntName : string) (prod : production) (tokens : list string) (subtrees : list ast),
    In prod g /\ derivesList (rhs prod) tokens subtrees /\ lhs prod = (NT ntName) ->
    derives (NT ntName) tokens (Node ntName subtrees)

with derivesList {g : grammar} : list symbol -> list string -> list ast -> Prop :=
     | derivesNil  : derivesList nil nil nil
     | derivesCons :
         forall (hdRoot : symbol) (prefix : list string) (hdSubtree : ast),                  
           derives hdRoot prefix hdSubtree ->
           
           forall (tlRoots : list symbol) (suffix : list string) (tlSubtrees : list ast),
             derivesList tlRoots suffix tlSubtrees ->
             
             derivesList (hdRoot :: tlRoots) (prefix ++ suffix) (hdSubtree :: tlSubtrees).

Definition g := [(NT "noun phrase", [T "the" ; T "tiger"])].

(* This proof shouldn't succeed, because there's no grammar with the production 
   NT "noun phrase" -> [T "the" ; T "tiger"] *)
(* Edit -- now it does succeed, because I've added the notion of a grammar to the "derives" definition. *)
Example foo : (@derives g) (NT "noun phrase") ["the" ; "tiger"] (Node "noun phrase" [Leaf "the" ; Leaf "tiger"]).
Proof.
  apply derivesNT with (prod := (NT "noun phrase", [T "the" ; T "tiger"])).
  split.
  - simpl. left. reflexivity.
  - simpl. split.
    + apply derivesCons with (prefix := ["the"]).
      { apply derivesT. }
      { apply derivesCons with (prefix := ["tiger"]).
        apply derivesT.
        apply derivesNil. }
    + reflexivity.
Defined.                                
       
    