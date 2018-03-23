Require Import Bool List Omega String.
Require Import Grammar Lib.Tactics Lib.Utils.

Lemma find_In : forall k vT (v : vT) m,
    SymbolMap.find k m = Some v ->
    SymbolMap.In k m.
Proof.
  intros. rewrite SymbolMapFacts.in_find_iff. rewrite H.
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
  forall (gamma : list symbol) (X : string),
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
         (X : string),
    forallb isT gamma = true ->
    gamma <> (prefix ++ NT X :: suffix)%list.
Proof.
  unfold not; intros.
  apply NT_not_in_T_list with (X := X) in H.
  apply H; clear H.
  rewrite H0. rewrite in_app_iff.
  right. apply in_eq.
Qed.

(* A bunch of list and set lemmas that I probably won't need *)

Lemma empty_nil : forall s,
    SymbolSet.Empty s <-> SymbolSet.elements s = nil.
Proof. 
  intros; split; intros.
  - destruct (SymbolSet.elements s) as [| e es] eqn:Hs.
    + reflexivity.
    + exfalso. 
      unfold SymbolSet.Empty in H; eapply H; clear H.
      assert (SetoidList.InA eq e (SymbolSet.elements s)).
      { rewrite Hs; constructor; reflexivity. }
      eapply SymbolSetFacts.elements_iff. eassumption.
  - unfold SymbolSet.Empty; unfold not; intros e Hin.
    rewrite SymbolSetFacts.elements_iff in Hin. 
    rewrite H in Hin. inv Hin.
Qed.

Lemma list_remove_le : forall (x : symbol) (ys : list symbol),
    List.length (remove symbol_eq_dec x ys) <= List.length ys.
Proof.
  intros. induction ys as [| y ys]; simpl.
  - reflexivity.
  - destruct (symbol_eq_dec x y); simpl; omega.
Qed.

Lemma list_remove_lt : forall (x : symbol) (ys : list symbol),
    List.In x ys -> 
    List.length (remove symbol_eq_dec x ys) < List.length ys.
Proof.
  intros. induction ys as [| y ys]; simpl.
  - inv H.
  - destruct (symbol_eq_dec x y) as [Heq | Hneq]; simpl.
    + pose proof list_remove_le as Hle.
      specialize Hle with (x := x) (ys := ys). omega.
    + apply lt_n_S. apply IHys. clear IHys.
      simpl in H. destruct H as [Hhd | Htl].
      * exfalso. apply Hneq. symmetry. assumption.
      * assumption.
Qed.

Lemma cardinal_length : forall s s',
    SymbolSet.cardinal s' < SymbolSet.cardinal s <-> 
    List.length (SymbolSet.elements s') < List.length (SymbolSet.elements s).
Proof.
  intros. split; intros.
  - repeat rewrite <- SymbolSet.cardinal_spec. assumption.
  - repeat rewrite SymbolSet.cardinal_spec. assumption.
Qed.

Lemma remove_not_In : forall x ys,
    ~In x ys <-> remove symbol_eq_dec x ys = ys.
Proof.
  intros; split; unfold not; intros.
  - induction ys; simpl.
    + reflexivity.
    + destruct (symbol_eq_dec x a); simpl.
      * exfalso. subst. apply H. apply in_eq.
      * assert (Htls : remove symbol_eq_dec x ys = ys).
      { apply IHys; intros; clear IHys.
        apply H. apply in_cons. assumption. }
      rewrite Htls; reflexivity.
  - rewrite <- H in H0. eapply remove_In. eassumption.
Qed.             

Lemma removeOptDecreasing :
  forall (x : symbol) (s s' : SymbolSet.t),
    removeOpt x s = Some s' ->
    SymbolSet.cardinal s' < SymbolSet.cardinal s.
Proof.
  intros. unfold removeOpt in H. 
  destruct (SymbolSet.mem x s) eqn:Hmem.
  - inv H.
    pose proof SymbolSetEqProps.remove_cardinal_1.
    apply H in Hmem. clear H. omega.
  - inv H.
Qed.

Lemma eq_sym_eq_T : 
  forall (s s2 : string),
    beqSym (T s) (T s2) = true <-> s = s2.
Proof.
  split; intro H.
  - unfold beqSym in H.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2))
      as [Heq | Hneq].
    + inv Heq; reflexivity.
    + inv H.
  - unfold beqSym.
    destruct (SymbolMapFacts.eq_dec (T s) (T s2))
      as [Heq | Hneq].
    + reflexivity.
    + exfalso. apply Hneq. subst. reflexivity.
Qed.