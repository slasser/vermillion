Require Import ExampleGrammars.
Require Import Grammar.
Require Import List.
Require Import MSets.
Require Import ParserTactics.
Require Import ParseTable.
Require Import String.
Import ListNotations.
Open Scope string_scope.

(* Tests use Grammar 3.12, shown here:

     Z -> d
     Z -> X Y Z
     Y -> []
     Y -> c
     X -> Y
     X -> a

 *)

(* Tests of NULLABLE set definitions *)

(* Correct NULLABLE set for g312:

   {X, Y}                              

*)
Definition g312NullableSet :=
  (SymbolSet.add (NT "X")
                 (SymbolSet.add (NT "Y")
                                SymbolSet.empty)).

Example g312NullableSetCorrect :
  isNullableSetFor g312NullableSet g312.
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
            { inv H1. rewrite <- SymbolSet.mem_spec.
              reflexivity. }
            { inv H1.
              { inv H. inv H0. }
              { inv H. }}}}
  - unfold nSetMinimal. intros. inv H.
    + subst. unfold g312. exists nil. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
    + (* Not exactly sure how to use InA, but this works. *)
      rewrite InA_singleton in H1; subst.
      unfold g312. exists [NT "Y"]. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
Defined.

Hint Resolve g312NullableSetCorrect.

(* Tests of FIRST set definitions *)

Ltac crush :=
  repeat match goal with
         | |- ?X = ?X => reflexivity
         | H : [] = _ ++ (_ :: _) |- _ =>
           apply app_cons_not_nil in H
         | H : false = true |- _ => inv H
         | H : False |- _ => inv H
         | H : SymbolMap.In _ _ |- _ => inv H
         | H : SymbolMap.Raw.PX.MapsTo _ _ _ |- _ => inv H
         | H : SymbolMap.Raw.PX.eqke _ _ |- _ => inv H
         | H : NT _ = NT _ |- _ => inv H
         | H : T _ = T _ |- _ => inv H
           (* Good approach? *)
         | H : SymbolMap.find (NT ?X) _ = Some _ |- _ =>
           match X with
           | String _ _ => inv H
           | _          => fail
           end
         | H : SymbolSet.In (T _) _ |- _ => inv H
         | H : _ :: _ = _ :: _ |- _ => inv H
         | |- List.In _ _ =>
           repeat (try (left; reflexivity); right)
         | |- forallb _ _ = true => reflexivity
         | H : InA _ _ (T _ :: _) |- _ => inv H
         | H : InA _ _ nil |- _ => inv H
         | H : InA _ (pair _ _) (pair _ _ :: _) |- _ =>
           inv H
         | H : _ \/ _ |- _ => inv H
         | H : pair (NT _) _ = pair (NT _) _ |- _ =>
           inv H
         | |- InA _ _ (_ :: _) =>
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)
         | _ => simpl in *
         | |- _ /\ _ => split
         | |- SymbolMap.find _ _ = Some _ =>
           unfold SymbolMap.find; reflexivity
         | |- (String _ _) <> (String _ _) =>
           unfold not; intros
         end.

(* FIRST sets for each nonterminal in Grammar 3.12 *)
Definition cSet   := SymbolSet.add (T "c") SymbolSet.empty.
Definition acSet  := SymbolSet.add (T "a") cSet.
Definition acdSet := SymbolSet.add (T "d") acSet.

(* Correct FIRST set for Grammar 3.12 *)
Definition g312FirstSet :=
  SymbolMap.add
    (NT "X") acSet
    (SymbolMap.add
       (NT "Y") cSet
       (SymbolMap.add
          (NT "Z") acdSet
          (SymbolMap.empty SymbolSet.t))).

Create HintDb g312Hints.

Example Y_c_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "Y") (T "c").
Proof.
  apply firstT with (prefix := nil) (suffix := nil); crush; auto.
Defined.
Hint Resolve Y_c_in_First : g312Hints.

Example X_a_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "X") (T "a").
Proof.
  apply firstT with (prefix := nil) (suffix := nil); crush; auto.
Defined.
Hint Resolve X_a_in_First : g312Hints.

Example X_c_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "X") (T "c").
Proof.
  apply firstNT with
      (prefix := nil)
      (rightX := "Y")
      (suffix := nil); crush; auto with g312Hints.
  unfold not; intros; inv H.
Defined.
Hint Resolve X_c_in_First : g312Hints.

Example Z_a_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "a").
Proof.
  apply firstNT with
      (rightX := "X")
      (prefix := nil)
      (suffix := [NT "Y" ; NT "Z"]);
    crush; auto with g312Hints.
  unfold not; intros; inv H.
Defined.
Hint Resolve Z_a_in_First : g312Hints.

Example Z_c_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "c").
Proof.
  apply firstNT with
      (rightX := "Y")
      (prefix := [NT "X"])
      (suffix := [NT "Z"]); crush; auto with g312Hints.
  unfold not; intros; inv H.
Defined.
Hint Resolve Z_c_in_First : g312Hints.

Example Z_d_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "d").
Proof.
  apply firstT with (prefix := nil) (suffix := nil); crush; auto.
Defined.
Hint Resolve Z_d_in_First : g312Hints.

Lemma find_In : forall k vT (v : vT) m,
    SymbolMap.find k m = Some v ->
    SymbolMap.In k m.
Proof.
  intros. rewrite SymbolMapFacts.in_find_iff.
  rewrite H. unfold not.
  intros. inv H0.
Defined.

Definition isNT sym := match sym with
                      | NT _ => true
                      | _    => false
                       end.

Definition isT sym := match sym with
                      | T _ => true
                      | _   => false
                      end.

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
Defined.

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
Defined.

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
Defined.

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
Defined.

Ltac crushGoal :=
  repeat match goal with
         | |- SymbolMap.find _ _ = Some _ =>
           unfold SymbolMap.find; reflexivity
         | |- SymbolSet.In _ _ =>
           subst;
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)
         | |- forallb _ _ = true => compute; reflexivity
         | |- In (String _ _) _ =>
           repeat (try (left; reflexivity); right)
         end.

Ltac crushContra :=
  repeat match goal with
         | H : [NT _] = (_ ++ T _ :: _)%list |- ?G =>
           match G with
           | exists _, _ /\ _ =>
             apply NT_list_neq_list_with_T in H; inv H; clear H
           | SymbolSet.In _ _ =>
             apply NT_list_neq_list_with_T in H; inv H; clear H
           | _ => fail
           end
         | H : [T _] = (_ ++ NT _ :: _)%list |- ?G =>
           match G with
           | exists _, _ /\ _ =>
             apply T_list_neq_list_with_NT in H;
             inv H; clear H
           | SymbolSet.In _ _ =>
             apply T_list_neq_list_with_NT in H;
             inv H; clear H
           | _ => fail
           end
         | H : [] = (_ ++ _ :: _)%list |- _ =>
           apply app_cons_not_nil in H; inv H
         | H : (String _ _ <> String _ _) |- _ =>
           exfalso; apply H; reflexivity
         | H : In _ [] |- _ => inv H
  end.

Ltac proveTerminalVal :=
  repeat match goal with
         | H : [T ?X] = (?prefix ++ T ?Y :: ?suffix)%list |-
           ?Y = ?X =>
           destruct prefix; destruct suffix;
           inv H; try reflexivity; crushContra
         end.

Ltac proveNonterminalVal :=
  repeat match goal with
         | H : [NT ?X] = (?prefix ++ NT ?Y :: ?suffix)%list |-
           ?Y = ?X =>
           destruct prefix; destruct suffix;
           inv H; try reflexivity; crushContra
  end.



Example g312FirstSetCorrect :
  isFirstSetFor g312FirstSet g312 g312NullableSet.
Proof.
  unfold isFirstSetFor. split.
  - (* firstSetComplete *)
    unfold firstSetComplete. intros.
    unfold g312FirstSet. inv H.
    + (* firstT case -- for each production with this form:
         NT X -> prefix ++ T y :: suffix
         prove that (X, y) is in the FIRST finite map *)
      crush.
      * (* Z -> d has the right form *)
        exists acdSet. split.
        { unfold SymbolMap.find; reflexivity. }
        { assert (y = "d").
          { destruct prefix; destruct suffix; crush. }
          rewrite H. compute. crush. }
      * (* Z -> X Y Z doesn't have the right form *)
        apply NT_list_neq_list_with_T in H2; crush.
      * (* Y -> [] doesn't have the right form *)
        apply app_cons_not_nil in H2; crush.
      * (* Y -> c has the right form *)
        exists cSet. split.
        { crushGoal. }
        { assert (y = "c").
          { destruct prefix; destruct suffix; crush. }
          rewrite H. crushGoal. }
      * (* X -> Y doesn't have the right form *)
        crushContra; crushGoal.
      * (* X -> a has the right form *)
        exists acSet. split.
        { crushGoal. }
        { assert (y = "a").
          { proveTerminalVal. }
          crushGoal. }
    + (* firstNT case -- for each production with this form:
 
         NT A -> prefix ++ NT B :: suffix

         ...prove that if (B, y) is in the FIRST finite map,
         then (A, y) is in the FIRST finite map *)
      crush.
      * (* Z -> d doesn't have the right form *)
        crushContra; crushGoal.
      * (* Z -> X Y Z has the right form --
           there are three possible bindings for B *)
        exists acdSet. split.
        { crushGoal. }
        { assert (In rightX ["X"; "Y"; "Z"]).
          { repeat match goal with
                   | H : (NT _ :: _) = (?P ++ NT _ :: _)%list
                     |- _ => destruct P; inv H;
                             crushGoal; crushContra
                   end. }
          inv H.
          { (* B := X *)
            inv H5; crush.
            { crushContra; crushGoal. }
            { assert (y = "a"); proveTerminalVal; crushGoal. }
            { assert (rightX = "Y"); proveNonterminalVal.
              subst. inv H8; crush; crushContra.
              { assert (y = "c"); proveTerminalVal;
                  crushGoal. }
              { crushGoal. }}
            { crushContra; crushGoal. }}
          inv H0.
          { (* B := Y *)
            inv H5; crush.
            { crushContra; crushGoal. }
            { assert (y = "c"); proveTerminalVal; crushGoal. }
            { crushContra. }
            { crushContra; crushGoal. }}
          inv H.
          { crushContra. }
          { crushContra. }}
      * (* Y -> [] has the wrong form *)
        crushContra.
      * (* Y -> c has the wrong form *)
        crushContra. crushGoal.
      * (* X -> Y has the right form, 
           and the only possible binding for B is Y. *)
        exists acSet. split.
        { crushGoal. }
        { assert (rightX = "Y"); proveNonterminalVal.
          subst. inv H5; crush.
          { crushContra. }
          { assert (y = "c"); proveTerminalVal; crushGoal. }
          { crushContra. }
          { crushContra. crushGoal. }}
      * (* X -> a has the wrong form *)
        crushContra. crushGoal.
  - (* firstSetMinimal *)
    unfold firstSetMinimal. intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. crush; auto with g312Hints.
Defined.

(* This shouldn't work -- maybe an iff is needed *)
(* Good news -- it doesn't work anymore! *)
Example isFirstSetForFlawed :
  isFirstSetFor
    (SymbolMap.empty SymbolSet.t) g312 g312NullableSet.
Proof.
  unfold isFirstSetFor. split.
  - unfold firstSetComplete. intros.
    inv H; crush.
    + exists acdSet. split.
      * unfold SymbolMap.find. simpl.
Abort.