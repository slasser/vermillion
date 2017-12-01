Require Import Derivation.
Require Import Grammar.
Require Import List.
Require Import Parser.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Definition input1 := ["if" ; "num" ; "==" ; "num" ; "then" ; "print" ; "num" ; "==" ; "num" ; "else" ; "print" ; "num" ; "==" ; "num"].
Example derivation1 : (@derives g311) (NT "S") input1 (Node "S" [Leaf "if" ;
                                                                 Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"] ;
                                                                 Leaf "then" ;
                                                                 Node "S" [Leaf "print" ;
                                                                           Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]] ;
                                                                 Leaf "else" ;
                                                                 Node "S" [Leaf "print" ;
                                                                           Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]]]).

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

Ltac crush := repeat match goal with
                     | |- _ /\ _ => split
                     | |- In _ _ => repeat (try (left ; reflexivity) ; right)
                     | |- derives (T _) _ _ => apply derivesT
                     | |- derivesList (T ?s :: _) _ _ => let tName := s
                                                         in  apply derivesCons with (prefix := [tName])
                     | |- derivesList [] _ _ => apply derivesNil
                     | |- ?P = ?P => reflexivity
                     | |- _ => simpl
                     end.

(* A more automated proof of the same derivation. *)
Example derivation2 : (@derives g311) (NT "S") input1 (Node "S" [Leaf "if" ;
                                                                 Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"] ;
                                                                 Leaf "then" ;
                                                                 Node "S" [Leaf "print" ;
                                                                           Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]] ;
                                                                 Leaf "else" ;
                                                                 Node "S" [Leaf "print" ;
                                                                           Node "E" [Leaf "num" ; Leaf "==" ; Leaf "num"]]]).
Proof.
  apply derivesNT with (prod := (NT "S", [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"])); crush.
  apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
  - apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); crush.
  - crush.
    apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
    + apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); crush.
      apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); crush.
      * crush.
    + crush.
      apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
      * apply derivesNT with (prod := (NT "S", [T "print" ; NT "E"])); crush.
        apply derivesCons with (prefix := ["num"; "=="; "num"]).
        { apply derivesNT with (prod := (NT "E", [T "num" ; T "==" ; T "num"])); crush. }
        { crush. }
      * crush.
Defined.