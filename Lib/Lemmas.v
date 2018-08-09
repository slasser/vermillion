Require Import Bool List Omega String.
Require Import Grammar Lib.Tactics Lib.Utils.

Lemma find_In : forall k vT (v : vT) m,
    NtMap.find k m = Some v ->
    NtMap.In k m.
Proof.
  intros. rewrite NtMapFacts.in_find_iff. rewrite H.
  unfold not. intro Hcontra. inv Hcontra.
Qed.

Lemma ntmap_find_in : forall k vT (v : vT) m,
    NtMap.find k m = Some v ->
    NtMap.In k m.
Proof.
  intros. rewrite NtMapFacts.in_find_iff. rewrite H.
  unfold not. intro Hcontra. inv Hcontra.
Qed.

Ltac copy_and_find_In H :=
  let Hfind := fresh "Hfind" in
  let Heq   := fresh "Heq" in 
  remember H as Hfind eqn:Heq; clear Heq;
  apply find_In in H.

Lemma T_not_in_NT_list :
  forall (gamma : list symbol) (y : string),
    forallb isNT gamma = true ->
    ~In (T y) gamma.
Proof.
  intro gamma.
  induction gamma; unfold not; simpl; intros.
  - assumption.
  - apply andb_true_iff in H. destruct H.
    destruct H0.
    + rewrite H0 in H. inv H.
    + apply IHgamma with (y := y) in H1.
      apply H1. apply H0.
Qed.

(* Some useful lemmas to remember : in_eq, in_cons *)
Lemma NT_list_neq_list_with_T :
  forall (gamma prefix suffix : list symbol)
         (y : string),
    forallb isNT gamma = true ->
    gamma <> (prefix ++ T y :: suffix)%list.
Proof.
  unfold not. intros.
  apply T_not_in_NT_list with (y := y) in H.
  apply H. clear H.
  rewrite H0. rewrite in_app_iff.
  right. apply in_eq.
Qed.

Lemma NT_not_in_T_list :
  forall (gamma : list symbol) (X : nonterminal),
    forallb isT gamma = true ->
    ~In (NT X) gamma.
Proof.
  intro gamma.
  induction gamma; unfold not; simpl; intros.
  - assumption.
  - apply andb_true_iff in H. destruct H.
    destruct H0.
    + rewrite H0 in H. inv H.
    + apply IHgamma with (X := X) in H1.
      apply H1. assumption.
Qed.

Lemma T_list_neq_list_with_NT :
  forall (gamma prefix suffix : list symbol)
         (X : nonterminal),
    forallb isT gamma = true ->
    gamma <> (prefix ++ NT X :: suffix)%list.
Proof.
  unfold not; intros.
  apply NT_not_in_T_list with (X := X) in H.
  apply H; clear H.
  rewrite H0. rewrite in_app_iff.
  right. apply in_eq.
Qed.

Lemma beqString_refl :
  forall (s : string),
    beqString s s = true.
Proof.
  intros.
  unfold beqString.
  destruct (string_dec s s) eqn:Hbeq; auto.
Qed.

Lemma beqString_eq :
  forall (s s2 : string),
    beqString s s2 = true <-> s = s2.
Proof.
  split; intros.
  - unfold beqString in H.
    destruct (string_dec s s2); auto.
    congruence.
  - unfold beqString.
    destruct (string_dec s s2); auto.
Qed.

