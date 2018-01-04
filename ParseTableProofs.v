Require Import ExampleGrammars.
Require Import Grammar.
Require Import List.
Require Import MSets.
Require Import Parser.
Require Import ParserTactics.
Import ListNotations.

Definition nSetComplete (nSet : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    In (x, ys) g ->
    forallb (nullable nSet) ys = true ->
    SymbolSet.In x nSet.

Definition nSetMinimal (nSet : SymbolSet.t) (g : grammar) : Prop :=
  forall (x : symbol) (ys : list symbol),
    SymbolSet.In x nSet ->
    exists (ys : list symbol),
      In (x, ys) g /\
      forallb (nullable nSet) ys = true.

Definition isNullableSetFor (nSet : SymbolSet.t) (g : grammar) : Prop :=
  nSetComplete nSet g /\ nSetMinimal nSet g.

Example isNullableSetForTest :
  isNullableSetFor
    (SymbolSet.add (NT "X") (SymbolSet.add (NT "Y") SymbolSet.empty))
    g312.
Proof.
  unfold isNullableSetFor. split.
  - unfold nSetComplete. intros. inv H.
    + inv H1. inv H0.
    + inv H1.
      * inv H. inv H0.
      * inv H.
        { inv H1. rewrite <- SymbolSet.mem_spec. reflexivity. }
        { inv H1.
          { inv H. inv H0. }
          { inv H.
            { inv H1. rewrite <- SymbolSet.mem_spec. reflexivity. }
            { inv H1.
              { inv H. inv H0. }
              { inv H. }}}}
  - unfold nSetMinimal. intros. inv H.
    + subst. unfold g312. exists [EPS]. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
    + (* Not exactly sure how to use InA, but this works. *)
      rewrite InA_singleton in H1; subst.
      unfold g312. exists [NT "Y"]. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
Defined.

(* Add inductive version here *)