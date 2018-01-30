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

(* We can now prove that an incomplete nullable set is incorrect *)
Example incompleteNullableSetIncorrect :
  ~isNullableSetFor (SymbolSet.add (NT "X") SymbolSet.empty) g312.
Proof.
  unfold not. intros. inv H. clear H1.
  unfold nullableSetComplete in H0.
  specialize H0 with (x := "Y").
  assert (~SymbolSet.In (NT "Y")
           (SymbolSet.add (NT "X") SymbolSet.empty)).
  { unfold not. intros. crush. inv H2. }
  apply H. apply H0.
  apply nullable_nt with (gamma := nil).
  - crush.
  - intros. inv H1.
  - apply nullable_nil.
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

Example c_in_First_Y :
  (@firstSym g312) (T "c") (NT "Y").
Proof.
  apply first_nt with (ys := [T "c"]).
  - reflexivity.
  - crush.
  - apply fprod_hd.
    + unfold not; intros; inv H.
    + apply first_t. reflexivity.
Defined.

Example a_in_First_X :
  (@firstSym g312) (T "a") (NT "X").
Proof.
  apply first_nt with (ys := [T "a"]); crush.
  apply fprod_hd.
  - crush.
  - apply first_t. crush.
Defined.

Example c_in_First_X :
  (@firstSym g312) (T "c") (NT "X").
Proof.
  apply first_nt with (ys := [NT "Y"]); crush.
  apply fprod_hd.
  - unfold not; intros; inv H.
  - apply c_in_First_Y.
Defined.

Ltac provePairNotInFirst :=
  repeat match goal with
         | H : In (NT (String _ _), _) g312 |- _ => inv H
         | H : In (NT _, _) (_::_) |- _ => inv H
         | H : (NT (String _ _), _) = (NT (String _ _), _) |- _ => inv H
         | H : firstSym (T (String _ _)) (NT (String _ _)) |- _ => inv H

        | H : firstSym (T (String _ _)) (T (String _ _)) |- _ => inv H                                                               
         | H : firstProd (T (String _ _)) _ (_::_)  |- _ => inv H
         | H : firstProd _ _ nil |- _ => inv H
         | H : ParserUtils.isNT (T _) = true |- _ => inv H
         | H : In _ [] |- _ => inv H
         end.

(* Make sure we can also prove that a pair is not in FIRST *)
Example d_not_in_First_X :
  ~(@firstSym g312) (T "d") (NT "X").
Proof.
  unfold not. intros.
  provePairNotInFirst.
Defined.

Example a_in_First_Z :
  (@firstSym g312) (T "a") (NT "Z").
Proof.
  apply first_nt with (ys := [NT "X"; NT "Y"; NT "Z"]); crush.
  apply fprod_hd; crush.
  apply a_in_First_X.
Defined.

Example c_in_First_Z :
  (@firstSym g312) (T "c") (NT "Z").
Proof.
  apply first_nt with (ys := [NT "X"; NT "Y"; NT "Z"]); crush.
  apply fprod_tl.
  - apply X_nullable'.
  - apply fprod_hd; crush.
    apply c_in_First_Y.
Defined.
  
Example d_in_First_Z :
  (@firstSym g312) (T "d") (NT "Z").
Proof.
  apply first_nt with (ys := [T "d"]); crush.
  apply fprod_hd; crush.
Defined.

Lemma find_In : forall k vT (v : vT) m,
    SymbolMap.find k m = Some v ->
    SymbolMap.In k m.
Proof.
  intros. rewrite SymbolMapFacts.in_find_iff. rewrite H.
  unfold not. intro Hcontra. inv Hcontra.
Defined.

(* Much nicer than the proof of the same proposition below! *)
Example g312FirstSetCorrect :
  isFirstSetFor g312FirstSet g312.
Proof.
  unfold isFirstSetFor. split.
  - unfold firstSetComplete. intros. inv H0.
    + crush. (* x can't be both NT and T *)
    + crush.
      * exists acdSet. crush.
      * exists acdSet. crush.
      * exists acdSet. crush.
      (* Why do I have to prove this twice? *)
      * exists acdSet. crush.
      * exists cSet. crush.
      * exists acSet. crush.
      * exists acSet. crush.
  - unfold firstSetMinimal. intros. 
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. inv H.
    crush.
    + apply c_in_First_Z.
    + apply a_in_First_Z.
    + apply d_in_First_Z.
    + apply c_in_First_Y.
    + apply c_in_First_X.
    + apply a_in_First_X.
Defined.

Definition g312FirstSetPlus :=
  SymbolMap.add
    (NT "X") acdSet (* d shouldn't be in there *)
    (SymbolMap.add
       (NT "Y") cSet
       (SymbolMap.add
          (NT "Z") acdSet
          (SymbolMap.empty SymbolSet.t))).

(* We can also prove that a FIRST set with extraneous elements
   is not the correct FIRST set for Grammar 3.12 *)
Example nonMinimalFirstSetIncorrect :
  ~isFirstSetFor g312FirstSetPlus g312.
Proof.
  unfold not. intros. unfold isFirstSetFor in H. destruct H.
  clear H. unfold firstSetMinimal in H0.
  specialize H0 with (x := NT "X")
                     (xFirst := acdSet)
                     (y := T "d").
  assert (~(@firstSym g312) (T "d") (NT "X")).
  { unfold not. intros.
    inv H. crush. }
  apply H. apply H0.
  - crush.
  - crush.
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

Ltac proveTerminalBinding :=
  match goal with
  | H : [?X] = (?prefix ++ ?Y :: ?suffix)%list |-
    ?Y = ?X =>
    destruct prefix; inv H
  end.

Example finiteFollowCorrect :
  isFollowSetFor g312FollowSet g312.
Proof.
  unfold isFollowSetFor. split.
  - unfold followSetComplete. intros. inv H.
    + crush.
      * assert (x = T "d").
        { proveTerminalBinding; crush. }
        subst. crush.
      * destruct prefix; crush; exists acdSet; crush.
        { destruct prefix; crush.
          assert (suffix = nil).
          { destruct prefix.
            { inv H4. crush. }
            inv H4. crush. }
          subst. crush. }
        destruct prefix; crush.
        assert (suffix = nil).
          { destruct prefix.
            { inv H4. crush. }
            inv H4. crush. }
          subst. crush.
      * assert (x = T "c").
        { proveTerminalBinding; crush. }
        subst. crush.
      * assert (suffix = nil).
          { destruct prefix.
            { inv H4. crush. }
            inv H4. crush. }
          subst. crush.
      * assert (x = T "a").
        { proveTerminalBinding; crush. }
        subst; crush.
    + crush.
      * assert (x = T "d").
        { proveTerminalBinding; crush. }
        subst; crush.
      * destruct prefix; crush.
        { exfalso. inv H3. inv H6.
          apply Z_not_nullable'. assumption. }
        destruct prefix; crush.
        { exfalso. inv H3. apply Z_not_nullable'. assumption. }
        assert (x = NT "Z").
        { proveTerminalBinding; crush. }
        subst. crush.
      * assert (x = T "c").
        { proveTerminalBinding; crush. }
        subst; crush.
      * assert (x = NT "Y").
        { proveTerminalBinding; crush. }
        subst. exists acdSet. crush.
        inv H4.
        { crush.
          { destruct prefix0; crush. }
          destruct prefix0; crush.
          { destruct prefix0; crush.
            destruct prefix0; crush. }
          destruct prefix0; crush. destruct prefix0; crush.
          destruct prefix0; crush. }
        inv H.
        { crush. destruct prefix0; crush. }
        crush.
        { destruct prefix0; crush.
          { inv H7. inv H10.
            exfalso. apply Z_not_nullable'. assumption. }
          destruct prefix0; crush. destruct prefix0; crush. }
        destruct prefix0; crush.
      * assert (x = T "a").
        { proveTerminalBinding; crush. }
        subst; crush.
  - unfold followSetMinimal. intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. inv H.
    crush.
    + apply followRight with (lx := NT "Z")
                             (prefix := [NT "X"])
                             (suffix := [NT "Z"]).
      * crush.
      * crush.
      * apply fgamma_hd. apply c_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := [NT "X"])
          (suffix := [NT "Z"]); crush.
      apply fgamma_hd. apply a_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := [NT "X"])
          (suffix := [NT "Z"]); crush.
      * apply fgamma_hd. apply d_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := nil)
          (suffix := [NT "Y"; NT "Z"]); crush.
      apply fgamma_hd. apply c_in_First_Y.
    + apply followRight with
          (lx := NT "Z")
          (prefix := nil)
          (suffix := [NT "Y"; NT "Z"]); crush.
      apply fgamma_tl.
      * apply Y_nullable'.
      * apply fgamma_hd. apply a_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := nil)
          (suffix := [NT "Y"; NT "Z"]); crush.
      apply fgamma_tl.
      * apply Y_nullable'.
      * apply fgamma_hd. apply d_in_First_Z.
Defined.

(* The next tests use Grammar 3.11, shown here:

   S -> if E then S else S
   S -> begin S L
   S -> print E

   L -> end
   L -> ; S L

   E -> num = num

 *)

Definition S_map :=
  SymbolMap.add
    (T "if")
    (NT "S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"])
    (SymbolMap.add
       (T "begin")
       (NT "S", [T "begin"; NT "S"; NT "L"])
       (SymbolMap.add
          (T "print")
          (NT "S", [T "print"; NT "E"])
          (SymbolMap.empty (symbol * list symbol)))).

Definition L_map :=
  SymbolMap.add
    (T "end")
    (NT "L", [T "end"])
    (SymbolMap.add
       (T ";")
       (NT "L", [T ";"; NT "S"; NT "L"])
       (SymbolMap.empty (symbol * list symbol))).

Definition E_map :=
  SymbolMap.add
    (T "num")
    (NT "E", [T "num"; T "=="; T "num"])
    (SymbolMap.empty (symbol * list symbol)).

Definition g311ParseTable :=
  SymbolMap.add
    (NT "S") S_map
    (SymbolMap.add
       (NT "L") L_map
       (SymbolMap.add
          (NT "E") E_map
          (SymbolMap.empty (SymbolMap.t (symbol * list symbol))))).

Ltac copy_and_find_In H :=
  let Hfind := fresh "Hfind" in
  let Heq   := fresh "Heq" in 
  remember H as Hfind eqn:Heq; clear Heq;
  apply find_In in H.

Example g311ParseTableCorrect :
  isParseTableFor g311ParseTable g311.
Proof.
  unfold isParseTableFor. split.
  - unfold parseTableComplete. split.
    + unfold ptCompleteFirst. intros.
      inv H.
      * inv H1. exists S_map. split.
        { compute. crush. }
        inv H0.
        { inv H2.
          { compute. crush. }
          crush. }
        inv H3.
      * inv H1.
        { inv H. exists S_map. split.
          { compute. crush. }
          { inv H0.
            { inv H2.
              { crush. }
              crush. }
            inv H3. }}
        inv H.
        { inv H1. exists S_map. crush.
          { split.
            { crush. }
            crush. }
          { split.
            { crush. }
            inv H3. }
          { inv H3. }
          split.
          { crush. }
          inv H3. }
        inv H1.
        { inv H.
          exists L_map. split.
          { crush. }
          crush. }
        inv H.
        { inv H1. exists L_map. split.
          { compute. crush. }
          inv H0.
          { inv H2.
            { crush. }
            crush. }
          inv H3. }
        crush.
        { exists E_map. split.
          { compute; crush. }
          crush. }
        { inv H3. }
        inv H3.
    + unfold ptCompleteFollow. intros. inv H.
      * inv H2. inv H0. inv H3.
      * inv H2.
        { inv H. inv H0. inv H3. }
        inv H.
        { inv H2. inv H0. inv H3. }
        inv H2.
        { inv H. inv H0. inv H3. }
        inv H.
        { inv H2. inv H0. inv H3. }
        inv H2.
        { inv H. inv H0. inv H3. }
        inv H.
  - unfold parseTableMinimal. intros.
    remember H as Hfind. clear HeqHfind.
    apply find_In in H. inv H. crush.
    + remember H0 as Hfind. clear HeqHfind.
      apply find_In in H0. inv H0. crush. inv Hfind.
      left. apply fgamma_hd. apply first_t. reflexivity.
    + copy_and_find_In H0. inv H0. crush.
      * inv Hfind. left.
        apply fgamma_hd. crush.
      * inv Hfind. left.
        apply fgamma_hd. crush.
    + copy_and_find_In H0. inv H0. crush.
      * inv Hfind. left.
        apply fgamma_hd. crush.
      * inv Hfind. left.
        apply fgamma_hd. crush.
      * inv Hfind. left.
        apply fgamma_hd. crush.
Defined.
        
        
          
          
    





           
            