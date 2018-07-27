Require Import List String.
Require Import Lib.Derivation ExampleGrammars Grammar ParseTree Tactics.
Import ListNotations.
Open Scope string_scope.

(* Manual proof of a derivation (don't do this again) *)
Example derivesTest1 :
  (@derivesTree g311) (NT X) g311Sentence1 g311ParseTree1.
Proof.
  apply derivesNT with 
      (x := X)
      (gamma := [T "if" ; NT E ; T "then" ; NT X ; T "else" ; NT X]).
  - left. reflexivity.
  - apply derivesCons with (prefix := ["if"]).
    + apply derivesT.
    + apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := E)
            (gamma := [T "num" ; T "==" ; T "num"]).
        { repeat (try (left ; reflexivity) ; right). }
        { apply derivesCons with (prefix := ["num"]).
          { apply derivesT. }
          apply derivesCons with (prefix := ["=="]).
          { apply derivesT. }
          apply derivesCons with (prefix := ["num"]).
          { apply derivesT. }
          apply derivesNil. }
      * apply derivesCons with (prefix := ["then"]).
        { apply derivesT. }
        apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
        { apply derivesNT with 
              (x := X)
              (gamma := [T "print" ; NT E]).
          { repeat (try (left ; reflexivity) ; right). }
          apply derivesCons with (prefix := ["print"]).
          { apply derivesT. }
          apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
          { apply derivesNT with
                (x := E) 
                (gamma := [T "num" ; T "==" ; T "num"]).
            { repeat (try (left ; reflexivity) ; right). }
            apply derivesCons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesCons with (prefix := ["=="]).
            { apply derivesT. }
            apply derivesCons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesNil. }
          apply derivesNil. }
        apply derivesCons with (prefix := ["else"]).
        { apply derivesT. }
        apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
        { apply derivesNT with 
              (x := X)
              (gamma := [T "print" ; NT E]).
          { repeat (try (left ; reflexivity) ; right). }
          apply derivesCons with (prefix := ["print"]).
          { apply derivesT. }
          apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
          { apply derivesNT with 
                (x := E)
                (gamma := [T "num" ; T "==" ; T "num"]).
            { repeat (try (left ; reflexivity) ; right). }
            apply derivesCons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesCons with (prefix := ["=="]).
            { apply derivesT. }
            apply derivesCons with (prefix := ["num"]).
            { apply derivesT. }
            apply derivesNil. }
          apply derivesNil. }
        apply derivesNil.
Qed.

(* A (slightly) more automated proof of the same derivation. *)
Example derivesTest2 :
  (@derivesTree g311) (NT X) g311Sentence1 g311ParseTree1.
Proof.
  apply derivesNT with 
      (x := X)
      (gamma := [T "if" ; NT E ; T "then" ; NT X ; T "else" ; NT X]);
    derCrush.
  apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
  - apply derivesNT with 
        (x := E)
        (gamma := [T "num" ; T "==" ; T "num"]); derCrush.
  - derCrush.
    apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
    + apply derivesNT with 
          (x := X)
          (gamma := [T "print" ; NT E]); derCrush.
      apply derivesCons with (prefix := ["num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := E)
            (gamma := [T "num" ; T "==" ; T "num"]); derCrush.
      * derCrush.
    + derCrush.
      apply derivesCons with (prefix := ["print" ; "num" ; "==" ; "num"]).
      * apply derivesNT with 
            (x := X)
            (gamma := [T "print" ; NT E]); derCrush.
        apply derivesCons with (prefix := ["num"; "=="; "num"]).
        { apply derivesNT with 
              (x := E)
              (gamma := [T "num" ; T "==" ; T "num"]); derCrush. }
        derCrush.
      * derCrush.
Qed.

