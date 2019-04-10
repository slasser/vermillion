Require Import List
               MSets
               String.
Require Import Grammar.
Import ListNotations.
Open Scope string_scope.

Ltac inv H := inversion H; clear H; subst.

Ltac step_h := match goal with
               | H : context[match ?x with | _ => _ end] |- _ => destruct x
               end.

Ltac step_h_eq s := let Heq := fresh s in
                    match goal with
                    | H : context[match ?x with | _ => _ end] |- _ =>
                      destruct x eqn:Heq
                    end.

Ltac step_g := match goal with
               | |- context[match ?x with | _ => _ end] => destruct x
               end.

Ltac step_g_eq s := let Heq := fresh s in
                    match goal with
                    | |- context[match ?x with | _ => _ end] => destruct x eqn:Heq
                    end.

Ltac step := simpl in *; (first [step_h | step_g]); auto.
Ltac step_eq s := (first [step_h_eq s | step_g_eq s]); auto.
Ltac cr := repeat step.
Ltac cr_eq s := repeat (step_eq s).
Ltac tc := try congruence.

Ltac dm :=
  match goal with
  | H : context[match ?X with _ => _ end] |- _ => destruct X
  | |- context[match ?X with _ => _ end] => destruct X
  end.

Ltac invh :=
  match goal with
  | H : inl _ = inl _ |- _ => inv H
  | H : inr _ = inr _ |- _ => inv H
  end.

Ltac invhs := repeat invh.

(* Add this to crush *)
Ltac solveNotFalse := simpl; unfold not; intros; inversion H.

Ltac proveSymBinding :=
  match goal with
  | H : [?X] = (?prefix ++ ?Y :: ?suffix)%list |-
    ?Y = ?X =>
    destruct prefix; inv H
  end.