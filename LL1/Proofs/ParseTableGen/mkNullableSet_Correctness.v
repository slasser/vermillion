Require Import Lib.Grammar.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Theorem mkNullableSet_sound :
  forall (g : grammar)
         (nu : NtSet.t),
    mkNullableSet g = nu
    -> nullable_set_sound nu g.
Proof.
  intros g nu Hmk.
  unfold nullable_set_sound.
  intros x Hin.
  unfold mkNullableSet in Hmk.
Admitted.