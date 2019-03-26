Require Import List MSets String.
Require Import Derivation Grammar ParseTable Utils.
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