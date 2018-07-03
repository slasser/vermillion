Require Import ExampleGrammars.
Require Import Grammar.
Require Import Lemmas.
Require Import List MSets String.
Require Import ExampleGrammars Grammar Lemmas
               Tactics ParseTable Utils.
Import ListNotations.
Open Scope list_scope.

Lemma nullable_nonrec :
  forall g sym,
    (@nullable_sym g) sym
    -> exists gamma,
      (@nullable_prod g) sym gamma
      /\ ~In sym gamma.
Proof.
  intros g sym.
  induction 1 using nullable_sym_mutual_ind with
      (P := fun sym gamma (pf : nullable_prod sym gamma) =>
              exists gamma',
                (@nullable_prod g) sym gamma'
                /\ ~In sym gamma')
      (P0 := fun gamma (pf : nullable_gamma gamma) =>
               forall sym,
                 In sym gamma
                 -> exists gamma',
                   nullable_prod sym gamma'
                   /\ ~In sym gamma')
      (P1 := fun sym (pf : nullable_sym sym) =>
               exists gamma,
                 (@nullable_prod g) sym gamma
                 /\ ~In sym gamma); intros.
  - destruct (List.In_dec symbol_eq_dec (NT x) ys).
    + apply IHnullable_sym in i0.
      eauto.
    + exists ys.
      split; auto.
      constructor; auto.
  - inv H.
  - inv H0; eauto.
  - eauto.
Qed.
