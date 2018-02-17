Require Import List String.
Require Import Derivation ExampleGrammars Grammar ParseTree Tactics.
Import ListNotations.
Open Scope string_scope.

(* Manual proof of a derivation (don't do this again) *)
Example derivesTest1 :
  (@derivesTree g311) (NT "S") g311Sentence1 g311ParseTree1.
Proof.
  apply derivesNT with 
      (x := "S")
      (gamma := [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"]).
  - left. reflexivity.
  - apply derivesFcons with (prefix := ["if"]).
    + apply derivesT.
    + apply derivesFcons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := "E")
            (gamma := [T "num" ; T "==" ; T "num"]).
        { repeat (try (left ; reflexivity) ; right). }
        { apply derivesFcons with (prefix := ["num"]).
          { apply derivesT. }
          apply derivesFcons with (prefix := ["=="]).
          { apply derivesT. }
          apply derivesFcons with (prefix := ["num"]).
          { apply derivesT. }
          apply derivesFnil. }
      * apply derivesFcons with (prefix := ["then"]).
        { apply derivesT. }
        apply derivesFcons with (prefix := ["print" ; "num" ; "==" ; "num"]).
        { apply derivesNT with 
              (x := "S")
              (gamma := [T "print" ; NT "E"]).
          { repeat (try (left ; reflexivity) ; right). }
          apply derivesFcons with (prefix := ["print"]).
          { apply derivesT. }
          apply derivesFcons with (prefix := ["num" ; "==" ; "num"]).
          { apply derivesNT with
                (x := "E") 
                (gamma := [T "num" ; T "==" ; T "num"]).
            { repeat (try (left ; reflexivity) ; right). }
            apply derivesFcons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesFcons with (prefix := ["=="]).
            { apply derivesT. }
            apply derivesFcons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesFnil. }
          apply derivesFnil. }
        apply derivesFcons with (prefix := ["else"]).
        { apply derivesT. }
        apply derivesFcons with (prefix := ["print" ; "num" ; "==" ; "num"]).
        { apply derivesNT with 
              (x := "S")
              (gamma := [T "print" ; NT "E"]).
          { repeat (try (left ; reflexivity) ; right). }
          apply derivesFcons with (prefix := ["print"]).
          { apply derivesT. }
          apply derivesFcons with (prefix := ["num" ; "==" ; "num"]).
          { apply derivesNT with 
                (x := "E")
                (gamma := [T "num" ; T "==" ; T "num"]).
            { repeat (try (left ; reflexivity) ; right). }
            apply derivesFcons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesFcons with (prefix := ["=="]).
            { apply derivesT. }
            apply derivesFcons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesFnil. }
          apply derivesFnil. }
        apply derivesFnil.
Defined.

(* A (slightly) more automated proof of the same derivation. *)
Example derivesTest2 :
  (@derivesTree g311) (NT "S") g311Sentence1 g311ParseTree1.
Proof.
  apply derivesNT with 
      (x := "S")
      (gamma := [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"]);
    derCrush.
  apply derivesFcons with (prefix := ["num" ; "==" ; "num"]).
  - apply derivesNT with 
        (x := "E")
        (gamma := [T "num" ; T "==" ; T "num"]); derCrush.
  - derCrush.
    apply derivesFcons with (prefix := ["print" ; "num" ; "==" ; "num"]).
    + apply derivesNT with 
          (x := "S")
          (gamma := [T "print" ; NT "E"]); derCrush.
      apply derivesFcons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := "E")
            (gamma := [T "num" ; T "==" ; T "num"]); derCrush.
      * derCrush.
    + derCrush.
      apply derivesFcons with (prefix := ["print" ; "num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := "S")
            (gamma := [T "print" ; NT "E"]); derCrush.
        apply derivesFcons with (prefix := ["num"; "=="; "num"]).
        { apply derivesNT with 
              (x := "E")
              (gamma := [T "num" ; T "==" ; T "num"]); derCrush. }
        derCrush.
      * derCrush.
Defined.

