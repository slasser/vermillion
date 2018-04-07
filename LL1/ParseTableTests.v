Require Import ExampleGrammars.
Require Import Grammar.
Require Import Lemmas.
Require Import List MSets String.
Require Import ExampleGrammars Grammar Lemmas
               Tactics ParseTable Utils.
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
  (StringSet.add
     "X"
     (StringSet.add
        "Y"
        StringSet.empty)).

Example Y_nullable :
  (@nullableSym g312) "Y".
Proof.
  apply nullable_nt with (gamma := nil).
  crush.
  + intros; crush.
  + constructor.
Qed.

Example X_nullable :
  (@nullableSym g312) "X".
Proof.
  apply nullable_nt with (gamma := [NT "Y"]).
  crush.
  - intros. inv H.
    + discriminate. 
    + crush.
  - apply nullable_cons.
    + apply Y_nullable.
    + apply nullable_nil.
Qed.

(* We can't prove this false statement, which is good *)
Example Z_nullable :
  (@nullableSym g312) "Z".
Proof.
  apply nullable_nt with (gamma := [NT "X"; NT "Y"; NT "Z"]). crush.
  - intros. inv H.
    + unfold not; intros; inv H.
    + inv H0.
      * unfold not; intros; inv H.
      * inv H.
        { (* stuck *)
Abort.

(* Even better, we can prove that a symbol is NOT nullable *)
Example Z_not_nullable :
  ~(@nullableSym g312) "Z".
Proof.
  unfold not. intros.
  inv H. inv H0. crush.
  eapply H1; trivial. crush.
Qed.

(* Now we're ready to prove that the Grammar 3.12 NULLABLE set
   is correct *)
Example g312NullableSetCorrect :
  isNullableSetFor g312NullableSet g312.
Proof.
  unfold isNullableSetFor. split.
  - unfold nullableSetComplete. intros.
    inv H. inv H0. crush.
    exfalso. 
    apply (H1 (NT "Z")); crush.
  - unfold nullableSetMinimal. intros.
    inv H.
    + apply Y_nullable.
    + apply InA_singleton in H1. subst.
      apply X_nullable.
Qed.

(* We can also prove that an incomplete nullable set is 
   incorrect *)
Example incompleteNullableSetIncorrect :
  ~isNullableSetFor
   (StringSet.singleton "X")
   g312.
Proof.
  unfold not. intros. inv H. clear H1.
  unfold nullableSetComplete in H0.
  specialize H0 with (x := "Y").
  assert (~StringSet.In "Y"
           (StringSet.add "X" StringSet.empty)).
  { unfold not. intros. crush. inv H2. }
  apply H. apply H0.
  apply nullable_nt with (gamma := nil).
  - crush.
    intros. inv H1. apply nullable_nil.
Qed.


(* Tests of FIRST set definitions *)


(* FIRST sets for each nonterminal in Grammar 3.12 *)
Definition cSet   := StringSet.add "c" StringSet.empty.
Definition acSet  := StringSet.add "a" cSet.
Definition acdSet := StringSet.add "d" acSet.

(* Correct FIRST set for Grammar 3.12 *)
Definition g312FirstSet :=
  StringMap.add
    "X" acSet
    (StringMap.add
       "Y" cSet
       (StringMap.add
          "Z" acdSet
          (StringMap.empty StringSet.t))).

Example c_in_First_Y :
  (@firstSym g312) "c" (NT "Y").
Proof.
  apply first_nt with (ys := [T "c"]).
  crush.
Qed.

Example a_in_First_X :
  (@firstSym g312) "a" (NT "X").
Proof.
  apply first_nt with (ys := [T "a"]); crush.
Qed.

Example c_in_First_X :
  (@firstSym g312) "c" (NT "X").
Proof.
  apply first_nt with (ys := [NT "Y"]); crush.
  apply fprod_hd; crush. 
  apply first_nt with (ys := [T "c"]); crush.
Qed.

(* We can also prove that a pair is not in FIRST *)
Example d_not_in_First_X :
  ~(@firstSym g312) "d" (NT "X").
Proof.
  unfold not. intros. crush.
Qed.

Example a_in_First_Z :
  (@firstSym g312) "a" (NT "Z").
Proof.
  apply first_nt with (ys := [NT "X"; NT "Y"; NT "Z"]);
  crush.
  apply fprod_hd; crush.
  apply a_in_First_X.
Qed.

Example c_in_First_Z :
  (@firstSym g312) "c" (NT "Z").
Proof.
  apply first_nt with (ys := [NT "X"; NT "Y"; NT "Z"]); crush.
  apply fprod_tl.
  - apply X_nullable.
  - apply fprod_hd; crush.
    apply c_in_First_Y.
Qed.
  
Example d_in_First_Z :
  (@firstSym g312) "d" (NT "Z").
Proof.
  apply first_nt with (ys := [T "d"]); crush.
Qed.

(* Much nicer than the proof of the same proposition below! *)
Example g312FirstSetCorrect :
  isFirstSetFor g312FirstSet g312.
Proof.
  unfold isFirstSetFor. split.
  - unfold firstSetComplete. intros. inv H.
    crush.
    + exists acdSet. crush.
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
    + apply c_in_First_Z.
    + apply a_in_First_Z.
    + apply d_in_First_Z.
    + apply c_in_First_Y.
    + apply c_in_First_X.
    + apply a_in_First_X.
Qed.

Definition g312FirstSetPlus :=
  StringMap.add
    "X" acdSet (* d shouldn't be in there! *)
    (StringMap.add
       "Y" cSet
       (StringMap.add
          "Z" acdSet
          (StringMap.empty StringSet.t))).

(* We can also prove that a FIRST set with extraneous elements
   is not the correct FIRST set for Grammar 3.12 *)
Example nonMinimalFirstSetIncorrect :
  ~isFirstSetFor g312FirstSetPlus g312.
Proof.
  unfold not. intros. unfold isFirstSetFor in H. destruct H.
  clear H. unfold firstSetMinimal in H0.
  specialize H0 with (x := "X")
                     (xFirst := acdSet)
                     (y := "d").
  assert (~(@firstSym g312) "d" (NT "X")).
  { unfold not. intros.
    inv H. crush. }
  apply H. apply H0.
  - crush.
  - crush.
Qed.


(* tests of FOLLOW definitions *)


(* Correct FOLLOW set for Grammar 3.12 *)
Definition g312FollowSet :=
  StringMap.add
    "X" acdSet
    (StringMap.add
       "Y" acdSet
       (StringMap.empty StringSet.t)).

Example finiteFollowCorrect :
  isFollowSetFor g312FollowSet g312.
Proof.
  unfold isFollowSetFor. split.
  - unfold followSetComplete. intros. inv H.
    + crush.
      * exists acdSet. crush.
      * exists acdSet. crush.
    + crush.
      * exfalso. apply Z_not_nullable. assumption.
      * exfalso. apply Z_not_nullable. assumption.
      * exists acdSet. crush.
  - unfold followSetMinimal. intros.
    copy_and_find_In H. inv H. crush.
    + apply followRight with
          (lx := NT "Z")
          (prefix := [NT "X"])
          (suffix := [NT "Z"]); crush.
      apply fgamma_hd. apply c_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := [NT "X"])
          (suffix := [NT "Z"]); crush.
      apply fgamma_hd. apply a_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := [NT "X"])
          (suffix := [NT "Z"]); crush.
      apply fgamma_hd. apply d_in_First_Z.
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
      * apply Y_nullable.
      * apply fgamma_hd. apply a_in_First_Z.
    + apply followRight with
          (lx := NT "Z")
          (prefix := nil)
          (suffix := [NT "Y"; NT "Z"]); crush.
      apply fgamma_tl.
      * apply Y_nullable.
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

Example g311ParseTableCorrect :
  isParseTableFor g311ParseTable g311.
Proof.
  unfold isParseTableFor. split.
  - unfold parseTableComplete. split.
    + unfold ptCompleteFirst. intros. crush.
      * exists S_map. crush.
      * exists S_map. crush.
      * exists S_map. crush.
      * exists L_map. crush.
      * exists L_map. crush.
      * exists E_map. crush.
    + unfold ptCompleteFollow. intros. crush.
  - unfold parseTableMinimal.
    intros  x tMap y gamma H_outer_find H_inner_find.
    copy_and_find_In H_outer_find.
    inv H_outer_find. crush.
    + copy_and_find_In H_inner_find.
      inv H_inner_find. crush.
      left. crush.
    + copy_and_find_In H_inner_find.
      inv H_inner_find. crush.
      * left. crush.
      * left. crush.
    + copy_and_find_In H_inner_find.
      inv H_inner_find. crush; left; crush.
Defined.

