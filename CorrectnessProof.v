Require Import Derivation.
Require Import Grammar.
Require Import List.
Require Import Parser.
Require Import String.
Import ListNotations.
Open Scope string_scope.

Ltac inv H := inversion H; clear H; subst.

Theorem epsilon_preserves_truth :
  forall (pt : M.t (M.t (list production)))
         (stack' : list symbol)
         (tokens : list string)
         (fuel : nat),
    parseLoop pt (EPS :: stack') tokens (S fuel) = true ->
    parseLoop pt stack' tokens fuel = true.
Proof.
  intros. inv H. reflexivity.
Defined.

Theorem terminal_match_preserves_truth :
  forall (pt : M.t (M.t (list production)))
         (tName : string)
         (stack' : list symbol)
         (token : string)
         (tokens : list string)
         (fuel : nat),
    parseLoop pt (T tName :: stack') (token :: tokens)
              (S fuel) = true ->
    parseLoop pt stack' tokens fuel = true.
Proof.
  intros. inv H. destruct (cmpSymbol (T tName) (T token)).
  - reflexivity.
  - inv H1.
Defined.

Theorem nonterminal_expansion_preserves_truth : 
  forall (pt : M.t (M.t (list production)))
         (ntName : string)
         (stack' : list symbol)
         (ys : list symbol)
         (token : string)
         (tokens : list string)
         (fuel : nat),
    parseLoop pt (NT ntName :: stack') (token :: tokens)
              (S fuel) = true ->
    exists (x : symbol) (ys : list symbol),
      ptLookup (NT ntName) (T token) pt = Some (x, ys) /\
      parseLoop pt (ys ++ stack') (token :: tokens) fuel = true.
Proof.
  intros. inv H.
  destruct (ptLookup (NT ntName) (T token)).
  - destruct p. exists s. exists l. split; reflexivity.
  - inversion H1.
Defined.

    
Theorem parse'_correct : forall (prefix : list string) (fuel : nat),
    parse' (mkParseTable g311 100) (NT "S") prefix fuel = true ->
    exists (pt : ast), @derives g311 (NT "S") prefix pt.
Proof. intros. induction fuel.
       - inversion H.
       - destruct prefix.
         + inversion H.


