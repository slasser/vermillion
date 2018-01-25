Require Import Derivation.
Require Import ExampleGrammars.
Require Import Grammar.
Require Import List.
Require Import ParseTree.
Require Import ParserTactics.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition input1 :=
  ["if" ; "num" ; "==" ; "num" ; "then" ; "print" ; "num" ; "==" ; "num" ; "else" ; "print" ; "num" ; "==" ; "num"].

Definition parseTree1 :=
  (Node "S" [Leaf "if" ;
             Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"] ;
             Leaf "then" ;
             Node "S" [Leaf "print" ;
                       Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]] ;
             Leaf "else" ;
             Node "S" [Leaf "print" ;
                       Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]]]).

(* Manual proof of a derivation (don't do this again) *)
Example derivesTest1 :
  (@derives g311) (NT "S") input1 parseTree1.
Proof.
  apply derivesNT with (prod := (NT "S", [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"])); simpl; split.
  - left. reflexivity.
  - split.
    + apply derivesCons with (prefix := ["if"]).
      * apply derivesT.
      * apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
        { apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); simpl; split.
          { repeat (try (left ; reflexivity) ; right). }
          { split.
            { apply derivesCons with (prefix := ["num"]).
              { apply derivesT. }
              { apply derivesCons with (prefix := ["=="]).
                { apply derivesT. }
                { apply derivesCons with (prefix := ["num"]).
                  { apply derivesT. }
                  { apply derivesNil. }}}}
            { reflexivity. }}}
        { apply derivesCons with (prefix := ["then"]).
          { apply derivesT. }
          { apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
            { apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); simpl ; split.
              { repeat (try (left ; reflexivity) ; right). }
              { split.
                { apply derivesCons with (prefix := ["print"]).
                  { apply derivesT. }
                  { apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
                    { apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); simpl; split.
                      { repeat (try (left ; reflexivity) ; right). }
                      { split.
                        { apply derivesCons with (prefix := ["num"]).
                          { apply derivesT. }
                          { apply derivesCons with (prefix := ["=="]).
                            { apply derivesT. }
                            { apply derivesCons with (prefix := ["num"]).
                              { apply derivesT. }
                              { apply derivesNil. }}}}
                        { reflexivity. }}}
                    { apply derivesNil. }}}
                { reflexivity. }}}
            { apply derivesCons with (prefix := ["else"]).
          { apply derivesT. }
          { apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
            { apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); simpl ; split.
              { repeat (try (left ; reflexivity) ; right). }
              { split.
                { apply derivesCons with (prefix := ["print"]).
                  { apply derivesT. }
                  { apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
                    { apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); simpl; split.
                      { repeat (try (left ; reflexivity) ; right). }
                      { split.
                        { apply derivesCons with (prefix := ["num"]).
                          { apply derivesT. }
                          { apply derivesCons with (prefix := ["=="]).
                            { apply derivesT. }
                            { apply derivesCons with (prefix := ["num"]).
                              { apply derivesT. }
                              { apply derivesNil. }}}}
                        { reflexivity. }}}
                    { apply derivesNil. }}}
                { reflexivity. }}}
            { apply derivesNil. }}}}}
    + reflexivity.
Defined.

(* A more automated proof of the same derivation. *)
Example derivesTest2 :
  (@derives g311) (NT "S") input1 parseTree1.
Proof.
  apply derivesNT with (prod := (NT "S", [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"])); derCrush.
  apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
  - apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush.
  - derCrush.
    apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
    + apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); derCrush.
      apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush.
      * derCrush.
    + derCrush.
      apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
      * apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); derCrush.
        apply derivesCons with (prefix := ["num"; "=="; "num"]).
        { apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush. }
        { derCrush. }
      * derCrush.
Defined.

(* Proof using the binary derivation relation, which doesn't include the notion
   of a parse tree or semantic value *)
Example derives2Test : (@derives2 g311) (NT "S") input1.
Proof.
  unfold input1.
  apply derivesNT2 with (prod := (NT "S", [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"])); derCrush.
  apply derivesCons2 with (prefix := ["num" ; "==" ; "num"]).
  - apply derivesNT2 with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush.
  - derCrush.
    apply derivesCons2 with (prefix := ["print" ; "num" ; "==" ; "num"]).
    + apply derivesNT2 with (prod := (NT "S", [T "print" ; NT "E"])); derCrush.
      apply derivesCons2 with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT2 with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush.
      * derCrush.
    + derCrush.
      apply derivesCons2 with (prefix := ["print" ; "num" ; "==" ; "num"]).
      * apply derivesNT2 with (prod := (NT "S", [T "print" ; NT "E"])); derCrush.
        apply derivesCons2 with (prefix := ["num"; "=="; "num"]).
        { apply derivesNT2 with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); derCrush. }
        { derCrush. }
      * derCrush.
Defined.