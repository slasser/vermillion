Require Import List.
Import ListNotations.

Section NoDup_dec.

  Variable A          : Type.
  Hypothesis eq_dec   : forall x y : A, {x = y} + {x <> y}.

  Fixpoint findDup (l : list A) : option A :=
    match l with
    | []      => None
    | x :: l' => match in_dec eq_dec x l' with
                 | left  _  => Some x
                 | right _  => findDup l'
                 end
    end.

  Lemma NoDup_findDup_None_iff : forall (l : list A), 
      NoDup l <-> findDup l = None.
  Proof.
    intros l; split; [intros Hn | intros Hf].
    - induction Hn as [| x l Hni Hnd IH]; simpl in *; auto.
      destruct (in_dec eq_dec x l); congruence.
    - induction l as [| x l' IH]; simpl in *.
      + constructor.
      + destruct (in_dec eq_dec x l') as [Hi | Hn]; try congruence.
        constructor; auto.
  Qed.

  Lemma NoDup_findDup_Some_iff : forall (l : list A),
      ~ NoDup l <-> exists (x : A), findDup l = Some x.
  Proof.
    intros l; split; [intros Hn | intros Hf].
    - destruct (findDup l) eqn:Hf; eauto.
      apply NoDup_findDup_None_iff in Hf; congruence.
    - unfold not; intros Hn.
      destruct Hf as [x Hf].
      apply NoDup_findDup_None_iff in Hn; congruence.
  Qed.

  Lemma NoDup_dec : 
    forall (l : list A), {NoDup l} + {~ NoDup l}.
  Proof.
    intros l.
    destruct (findDup l) eqn:Hu.
    - right; eapply NoDup_findDup_Some_iff; eauto.
    - apply NoDup_findDup_None_iff in Hu; auto.
  Qed.

End NoDup_dec.

