Require Import Derivation.
Require Import Grammar.
Require Import List.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

(* Add this to crush *)
Ltac solveNotFalse := simpl; unfold not; intros; inversion H. 

Ltac crush :=
  repeat match goal with
         | |- _ /\ _ => split
         | |- In _ _ => repeat (try (left ; reflexivity) ; right)
         | |- derives (T _) _ _ => apply derivesT
         | |- derives2 (T _) _  => apply derivesT2
         | |- derivesList (T ?s :: _) _ _ =>
           let tName := s
           in  apply derivesCons with (prefix := [tName])
         | |- derivesList2 (T ?s :: _) _  =>
           let tName := s
           in  apply derivesCons2 with (prefix := [tName])
         | |- derivesList [] _ _ => apply derivesNil
         | |- derivesList2 [] _  => apply derivesNil2
         | |- ?P = ?P => reflexivity
         | |- _ => simpl in *
         end.