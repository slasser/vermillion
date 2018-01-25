Require Import ExampleGrammars.
Require Import Grammar.
Require Import List.
Require Import MSets.
Require Import ParserTactics.
Require Import ParseTable.
Require Import ParserUtils.
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

(* The flawed NULLABLE definition can be used to prove a true
   statement... *)
Example g312NullableSetCorrect_first_try :
  flawedIsNullableSetFor g312NullableSet g312.
Proof.
  unfold isNullableSetFor. split.
  - unfold flawedNullableSetComplete. intros. inv H.
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
  - unfold flawedNullableSetMinimal. intros. inv H.
    + subst. unfold g312. exists nil. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
    + (* Not exactly sure how to use InA, but this works. *)
      rewrite InA_singleton in H1; subst.
      unfold g312. exists [NT "Y"]. split.
      * compute. repeat (try (left; reflexivity); right).
      * reflexivity.
Defined.

(* ...but this example shows that the non-relational 
   definition of NULLABLE is flawed *)
Definition weirdGrammar :=
  [(NT "X", [NT "Y"]);
     (NT "Y", [NT "X"])].

(* The NULLABLE set for this grammar should be empty, 
   but our NULLABLE definition lets us prove that it's not *)
Example nullableDefinitionFlawed :
  flawedIsNullableSetFor g312NullableSet weirdGrammar.
Proof.
  unfold flawedIsNullableSetFor. split.
  - unfold flawedNullableSetComplete. intros. crush.
  - unfold flawedNullableSetMinimal. intros. crush.
    + exists [NT "X"]. split.
      * crush.
      * compute; reflexivity.
    + exists [NT "Y"]. split.
      * crush.
      * simpl; reflexivity.
Defined.

(* We need a better definition of what it means for a symbol
   to be nullable. Here's one approach: *)

Example Y_nullable :
  (@flawedSymInNullableSet g312) (NT "Y").
Proof.
  apply nullableProd with (gamma := nil).
  - crush.
  - intros. inv H.
Defined.

Example X_nullable :
  (@flawedSymInNullableSet g312) (NT "X").
Proof.
  apply nullableProd with (gamma := [NT "Y"]).
  - crush.
  - intros. inv H.
    + split.
      * unfold not. intros. inv H.
      * apply Y_nullable.
    + inv H0.
Defined.

(* Shouldn't work *)
Example Z_nullable :
  (@flawedSymInNullableSet g312) (NT "Z").
Proof.
  apply nullableProd with (gamma := [NT "X"; NT "Y"; NT "Z"]).
  - crush.
  - intros. inv H.
    + split.
      * unfold not; intros; inv H.
      * apply X_nullable.
    + inv H0.
      * split.
        { unfold not; intros; inv H. }
        { apply Y_nullable. }
      * inv H.
        { split.
          { (* stuck *)
Abort.

(* This definition makes it harder to prove that a symbol is
   NOT nullable, though: *)
Example Z_not_nullable :
  ~(@flawedSymInNullableSet g312) (NT "Z").
Proof.
  unfold not. intros. inv H. inv H1.
  - inv H. specialize H2 with (sym := T "d").
Abort.

(* Here's a better approach: *)

Example Y_nullable' :
  (@nullableSym g312) (NT "Y").
Proof.
  apply nullable_nt with (gamma := nil).
  - crush.
  - intros. inv H.
  - apply nullable_nil.
Defined.

Example X_nullable' :
  (@nullableSym g312) (NT "X").
Proof.
  apply nullable_nt with (gamma := [NT "Y"]).
  - crush.
  - intros. inv H.
    + unfold not; intros; inv H.
    + inv H0.
  - apply nullable_cons.
    + apply Y_nullable'.
    + apply nullable_nil.
Defined.

(* We still can't prove this false statement, which is good *)
Example Z_nullable' :
  (@nullableSym g312) (NT "Z").
Proof.
  apply nullable_nt with (gamma := [NT "X"; NT "Y"; NT "Z"]).
  - crush.
  - intros. inv H.
    + unfold not; intros; inv H.
    + inv H0.
      * unfold not; intros; inv H.
      * inv H.
        { (* stuck *)
Abort.

(* ...but now we can also prove that a symbol is NOT nullable *)
Example Z_not_nullable' :
  ~(@nullableSym g312) (NT "Z").
Proof.
  unfold not. intros. inv H.
  inv H1.
  - inv H. inv H3. inv H1.
  - inv H.
    + inv H0. specialize H2 with (sym := NT "Z").
      apply H2.
      * crush.
      * reflexivity.
    + inv H0.
      { inv H. }
      inv H.
      { inv H0. }
      inv H0.
      { inv H. }
      inv H.
      { inv H0. }
      inv H0.
Defined.

(* Now we're ready to prove that the Grammar 3.12 NULLABLE set
   is correct *)
Example g312NullableSetCorrect :
  isNullableSetFor g312NullableSet g312.
Proof.
  unfold isNullableSetFor. split.
  - unfold nullableSetComplete. intros.
    inv H. inv H1.
    + inv H. inv H3. inv H1.
    + inv H.
      * exfalso. inv H0.
        specialize H2 with (sym := NT "Z").
        apply H2.
        { crush. }
        { reflexivity. }
      * inv H0.
        { inv H. compute. apply InA_cons_hd. reflexivity. }
        inv H.
        { inv H0. compute. apply InA_cons_hd. reflexivity. }
        inv H0.
        { inv H. compute. apply InA_cons_tl.
          apply InA_cons_hd. reflexivity. }
        inv H.
        { inv H0. compute. apply InA_cons_tl.
          apply InA_cons_hd. reflexivity. }
        inv H0.
  - unfold nullableSetMinimal. intros.
    inv H.
    + rewrite H1. apply Y_nullable'.
    + apply InA_singleton in H1. rewrite H1.
      apply X_nullable'.
Defined.

(* And now we can't prove that the NULLABLE set for the 
   weird grammar is non-empty, which is good *)
Example g312NullableSetCorrectForWeirdGrammar :
  isNullableSetFor g312NullableSet weirdGrammar.
Proof.
  unfold isNullableSetFor. split.
  - unfold nullableSetComplete. intros. inv H. inv H1.
    + inv H. compute. apply InA_cons_tl.
      apply InA_cons_hd. reflexivity.
    + inv H.
      * inv H0. compute. apply InA_cons_hd. reflexivity.
      * inv H0.
  - unfold nullableSetMinimal. intros. inv H.
    + rewrite H1. apply nullable_nt with (gamma := [NT "X"]).
      * crush.
      * intros. inv H.
        { unfold not; intros. inv H. }
        inv H0.
      * apply nullable_cons.
        { apply nullable_nt with (gamma := [NT "Y"]).
          { crush. }
          { intros. inv H.
            { unfold not; intros. inv H. }
            inv H0. }
          apply nullable_cons.
          { (* This will just keep going on forever *)
Abort.      

(* Tests of FIRST set definitions *)

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
  (@firstSym g312) (NT "Y") (T "c").
Proof.
  apply fi_nt with (gamma := [T "c"]).
  - crush.
  - apply fg_t. reflexivity.
Defined.

Example X_a_in_First :
  (@firstSym g312) (NT "X") (T "a").
Proof.
  apply fi_nt with (gamma := [T "a"]).
  - crush.
  - apply fg_t. reflexivity. 
Defined.

Example X_c_in_First :
  (@firstSym g312) (NT "X") (T "c").
Proof.
  apply fi_nt with (gamma := [NT "Y"]).
  - crush.
  - apply fg_nt_hd.
    + reflexivity.
    + unfold not; intros; inv H.
    + apply Y_c_in_First.
Defined.

Ltac provePairNotInFirst :=
  repeat match goal with
         | H : In (NT (String _ _), _) g312 |- _ => inv H
         | H : In (NT _, _) (_::_) |- _ => inv H
         | H : (NT (String _ _), _) = (NT (String _ _), _) |- _ => inv H
         | H : firstSym (NT (String _ _)) (T (String _ _)) |- _ => inv H
         | H : firstGamma _ (_::_) (T (String _ _)) |- _ => inv H
         | H : firstGamma _ nil _ |- _ => inv H
         | H : ParserUtils.isNT (T _) = true |- _ => inv H
         | H : In _ [] |- _ => inv H
         end.

(* Make sure we can also prove that a pair is not in FIRST *)
Example X_d_not_in_First :
  ~(@firstSym g312) (NT "X") (T "d").
Proof.
  unfold not. intros.
  provePairNotInFirst.
Defined.

Example Z_a_in_First :
  (@firstSym g312) (NT "Z") (T "a").
Proof.
  apply fi_nt with (gamma := [NT "X"; NT "Y"; NT "Z"]).
  - crush.
  - apply fg_nt_hd.
    + reflexivity.
    + unfold not; intros; inv H.
    + apply X_a_in_First.
Defined.

Example Z_c_in_First :
  (@firstSym g312) (NT "Z") (T "c").
Proof.
  apply fi_nt with (gamma := [NT "X"; NT "Y"; NT "Z"]).
  - crush.
  - apply fg_nt_tl.
    + reflexivity.
    + apply X_nullable'.
    + apply fg_nt_hd.
      * reflexivity.
      * unfold not; intros; inv H.
      * apply Y_c_in_First.
Defined.

Example Z_d_in_First :
  (@firstSym g312) (NT "Z") (T "d").
Proof.
  apply fi_nt with (gamma := [T "d"]).
  - crush.
  - apply fg_t. reflexivity.
Defined.

Lemma find_In : forall k vT (v : vT) m,
    SymbolMap.find k m = Some v ->
    SymbolMap.In k m.
Proof.
  intros. rewrite SymbolMapFacts.in_find_iff.
  rewrite H. unfold not.
  intros. inv H0.
Defined.

(* Much nicer than the proof of the same proposition below! *)
Example g312FirstSetCorrect :
  isFirstSetFor g312FirstSet g312.
Proof.
  unfold isFirstSetFor. split.
  - unfold firstSetComplete. intros. inv H. crush.
    + exists acdSet. crush.
    + exists acdSet. crush.
    + exists acdSet. crush.
    + exists cSet. crush.
    + exists acSet. crush.
    + exists acSet. crush.
  - unfold firstSetMinimal. intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. inv H.
    crush.
    + apply Z_c_in_First.
    + apply Z_a_in_First.
    + apply Z_d_in_First.
    + apply Y_c_in_First.
    + apply X_c_in_First.
    + apply X_a_in_First.
Defined.
    
Example old_Y_c_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "Y") (T "c").
Proof.
  apply firstPairT with (prefix := nil) (suffix := nil); crush; auto. apply g312NullableSetCorrect.
Defined.

Example old_X_a_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "X") (T "a").
Proof.
  apply firstPairT with (prefix := nil) (suffix := nil); crush; auto. apply g312NullableSetCorrect.
Defined.

Example old_X_c_in_First :
  (@pairInFirstSet g312 g312NullableSet) (NT "X") (T "c").
Proof.
  apply firstPairNT with
      (prefix := nil)
      (rightX := "Y")
      (suffix := nil); crush; auto with g312Hints.
  unfold not; intros; inv H. apply old_Y_c_in_First.
Defined.

Example old_Z_a_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "a").
Proof.
  apply firstPairNT with
      (rightX := "X")
      (prefix := nil)
      (suffix := [NT "Y" ; NT "Z"]);
    crush; auto with g312Hints.
  unfold not; intros; inv H.
  apply old_X_a_in_First.
Defined.

Example old_Z_c_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "c").
Proof.
  apply firstPairNT with
      (rightX := "Y")
      (prefix := [NT "X"])
      (suffix := [NT "Z"]); crush; auto with g312Hints.
  unfold not; intros; inv H.
  apply old_Y_c_in_First.
Defined.

Example old_Z_d_in_First :
  (@pairInFirstSet g312 g312NullableSet)
    (NT "Z") (T "d").
Proof.
  apply firstPairT with (prefix := nil) (suffix := nil); crush; auto. apply g312NullableSetCorrect.
Defined.

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

(* tests of FOLLOW definitions *)

(* Correct FOLLOW set for Grammar 3.12 *)
Definition g312FollowSet :=
  SymbolMap.add
    (NT "X") acdSet
    (SymbolMap.add
       (NT "Y") acdSet
       (SymbolMap.empty SymbolSet.t)).