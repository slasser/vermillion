Require Import ExampleGrammars.
Require Import Grammar.
Require Import List.
Require Import MSets.
Require Import Parser.
Require Import ParserTactics.
Require Import ParseTable.
Require Import String.
Import ListNotations.

(* Tests use Grammar 3.12, shown here:

     Z -> d
     Z -> X Y Z
     Y -> EPS
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
    + subst. unfold g312. exists [EPS]. split.
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
Defined.
Hint Resolve X_c_in_First : g312Hints.

Example Z_a_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "a").
Proof.
  apply firstNT with
      (rightX := "X")
      (prefix := nil)
      (suffix := [NT "Y" ; NT "Z"]); crush; auto with g312Hints.
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
  
Example g312FirstSetCorrect :
  isFirstSetFor g312FirstSet g312 g312NullableSet.
Proof.
  unfold isFirstSetFor. split.
  - (* pair in finite map implies pair in relation *)
    intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. crush.
    + (* Prove that Z -> c is in FIRST *)
      apply firstNT with
          (prefix := [NT "X"])
          (rightX := "Y")
          (suffix := [NT "Z"]); crush; auto.
      (* ...which involves proving that Y -> c is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "c")
          (suffix := nil); crush; auto.
    + (* Prove that Z -> a is in FIRST *)
      apply firstNT with
          (prefix := nil)
          (rightX := "X")
          (suffix := [NT "Y"; NT "Z"]); crush; auto.
      (* ...which involves proving that X -> a is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "a")
          (suffix := nil); crush; auto.
    + (* Prove that Z -> d is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "d")
          (suffix := nil); crush; auto.
    + (* Prove that Y -> c is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "c")
          (suffix := nil); crush; auto.
    + (* Prove that X -> c is in FIRST *)
      apply firstNT with
          (prefix := nil)
          (rightX := "Y")
          (suffix := nil); crush; auto.
      (* ...which involves proving that Y -> c is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "c")
          (suffix := nil); crush; auto.
    + (* Prove that X -> a is in FIRST *)
      apply firstT with
          (prefix := nil)
          (y      := "a")
          (suffix := nil); crush; auto.
  - (* pair in relation implies pair in finite set *)
    intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. crush.
    + (* If (pairInFirstSet Z y) for some y,
         then y is in the set {a, c, d} *)
      inv H0; crush.
      * (* current production : Z -> d 
           current pairInFirstSet constructor : firstT *)
          assert (y = "d").
          { destruct prefix; destruct suffix; crush. }
          rewrite H. compute. crush.
      * (* current production : Z -> X Y Z 
           current pairInFirstSet constructor : firstT *)
        apply NT_list_neq_list_with_T in H1; crush.
      * (* current production : Z -> d 
           current pairInFirstSet constructor : firstNT *)
        apply T_list_neq_list_with_NT in H1; crush.
      * (* current production : Z -> X Y Z 
           current pairInFirstSet constructor : firstNT *)
        destruct prefix.
        { crush. inv H5.
          { crush.
            { apply NT_list_neq_list_with_T in H1; crush. }
            { assert (y = "a").
              { destruct prefix; destruct suffix; crush. }
              rewrite H. compute. crush. }}
          { crush.
            { assert (rightX = "Y").
              { destruct prefix; destruct suffix; crush.
                { apply app_cons_not_nil in H5; crush. }
                { apply app_cons_not_nil in H5; crush. }}
              rewrite H in H7. inv H7. crush.
Abort.

(* This shouldn't work -- maybe an iff is needed *)
Example isFirstSetForFlawed :
  isFirstSetFor
    (SymbolMap.empty SymbolSet.t) g312 g312NullableSet.
Proof.
  unfold isFirstSetFor. intros.
  remember H as Hfind. clear HeqHfind.
  apply find_In in H. crush.
Defined.