Require Import List.
Require Import Wf_nat.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Import ListNotations.

Theorem mkFollowMap_sound :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_sound (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
Admitted.

Theorem mkFollowMap_complete :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_complete (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
Admitted.

Theorem mkFollowMap_correct :
  forall (g  : grammar)
         (nu : nullable_set)
         (fi : first_map)
         (nu_pf : nullable_set_for nu g)
         (fi_pf : first_map_for fi g),
    follow_map_for (mkFollowMap g nu fi fi_pf) g.
Proof.
  intros g nu fi Hnu Hfi.
  split.
  - apply mkFollowMap_sound; auto.
  - apply mkFollowMap_complete; auto.
Qed.
  