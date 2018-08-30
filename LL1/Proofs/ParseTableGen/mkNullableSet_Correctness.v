Require Import MSets.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.

Module MP := MSetProperties.Properties NtSet.

Lemma mkNullableSet'_eq_body :
  forall ps nu,
    mkNullableSet' ps nu =
    let nu' := nullablePass ps nu in
    if NtSet.eq_dec nu nu' then
      nu
    else
      mkNullableSet' ps nu'.
Proof.
  intros ps nu.
  unfold mkNullableSet'.
  unfold mkNullableSet'_func.
  rewrite Wf.fix_sub_eq; auto.
  intros.
  match goal with
  | |- context[NtSet.eq_dec ?a ?b] => destruct (NtSet.eq_dec a b)
  end; auto.
Qed.

Lemma mkNullableSet'_preserves_soundness :
  forall g nu,
    nullable_set_sound nu g
    -> nullable_set_sound (mkNullableSet' g.(productions) nu) g.
Proof.
  intros g nu Hsou.
  remember (NtSet.cardinal (NtSet.diff (lhSet g.(productions)) nu)) as card.
  generalize dependent g.
  generalize dependent nu.
  induction card as [| n]; intros nu g Hsou Heq.
  - admit.
  - 

Theorem mkNullableSet_sound :
  forall (g : grammar),
    nullable_set_sound (mkNullableSet g) g.
Proof.
  intros g.
  unfold nullable_set_sound.
  intros x Hin.
  unfold mkNullableSet in Hin.

  
  Lemma foo :
  forall g nu,
   nullable_set_for nu g
    \/ exists x,
      NtSet.In x (lhSet g.(productions))
      /\ ~NtSet.In x nu
      /\ NtSet.In x (nullablePass ps nu).