Require Import List MSets String.
Require Import Lib.Derivation Grammar ParseTable Lib.Utils.
Import ListNotations.
Open Scope string_scope.

Ltac inv H := inversion H; clear H; subst.

(* Add this to crush *)
Ltac solveNotFalse := simpl; unfold not; intros; inversion H.

Ltac proveSymBinding :=
  match goal with
  | H : [?X] = (?prefix ++ ?Y :: ?suffix)%list |-
    ?Y = ?X =>
    destruct prefix; inv H
  end.

Ltac derCrush :=
  repeat match goal with
         | |- _ /\ _ => split
         | |- In _ _ => repeat (try (left ; reflexivity) ; right)
         | |- derivesTree (T _) _ _ => apply derivesT
         | |- derivesForest (T ?s :: _) _ _ =>
           let tName := s
           in  apply derivesCons with (prefix := [tName])
         | |- derivesForest [] _ _ => constructor
         | |- ?P = ?P => reflexivity
         | |- _ => simpl in *
         end.