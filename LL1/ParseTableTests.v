Require Import List.
Require Import MSets.
Require Import String.

Require Import Lib.ExampleGrammars.
Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.

Ltac crush :=
  repeat match goal with
         (* inversions *)
         | H : InA _ _ [] |- _ => inv H
         | H : NT _ = NT _ |- _ => inv H
         | H : In _ _ |- _ => inv H
         | H : (String _ _, _) = (String _ _, _) |- _ => inv H
         | H : [] = _ ++ _ :: _ |- _ => apply app_cons_not_nil in H; inv H
         | H : _ = [] ++ _ :: _ |- _ => inv H
         | H : _ :: _ = (_ :: _) ++ _ |- _ => inv H
         | H : (_, _) = (_, _) |- _ => inv H
         | H : nullable_sym _ (T _) |- _ => inv H
         | H : nullable_gamma _ (_ :: _) |- _ => inv H
         | H : first_sym _ _ (T _) |- _ => inv H
         | H : first_sym _ _ (NT _) |- _ => inv H
         | H : SymbolMap.In _ (SymbolMap.add _ _ _) |- _ =>
           apply SymbolMapFacts.add_in_iff in H; inv H
         | H : SymbolMap.find (NT (String _ _)) _ = Some _ |- _ =>
           inv H
         | H : LookaheadSet.In _ _ |- _ => inv H
         | H : SymbolMap.In _ (SymbolMap.empty _) |- _ =>
           apply SymbolMapFacts.empty_in_iff in H; inv H

         (* goals *)
         | |- In _ _ => repeat (try (left; reflexivity); right)
         | |- nullable_gamma _ _ => constructor
         | |- first_sym _ _ _ => constructor
         | |- SymbolMap.find (NT (String _ _)) _ = _ => auto
         | |- LookaheadSet.In _ _ =>
           repeat (try (apply InA_cons_hd; reflexivity); apply InA_cons_tl)
         | |- Utils.isNT (NT _) = true => auto
         | |- _ /\ _ => split
         end.

Ltac crush' :=
  (match goal with
   | H : InA _ ?la _ |- first_sym _ ?la _  => inv H
   | H : _ :: _ = ?pre ++ ?y :: _ |- _ => destruct pre
  end); crush.

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

Definition fromSymList ys :=
  fold_right SymbolSet.add SymbolSet.empty ys.

Definition g312NullableSet := fromSymList [NT "X"; NT "Y"].

(*
Definition g312NullableSet :=
  (SymbolSet.add
     (NT "X")
     (SymbolSet.add
        (NT "Y")
        SymbolSet.empty)).
 *)

Example Y_nullable :
  (@nullable_sym g312) (NT "Y").
Proof.
  eapply NullableSym with (ys := []); crush.
Qed.

Example X_nullable :
  (@nullable_sym g312) (NT "X").
Proof.
  eapply NullableSym with (ys := [NT "Y"]); crush.
  apply Y_nullable.
Qed.

(* Nice -- with the new definitions of nullable_sym and
   nullable_gamma, we were able to complete this example
   without using a special "nullable_nonrec" lemma *)
Example Z_not_nullable :
  forall sym,
    (@nullable_sym g312) sym
    -> sym <> NT "Z".
Proof.
  unfold not; intros.
  revert H0.
  induction H using nullable_sym_mutual_ind with
      (P := fun sym (pf : nullable_sym g312 sym) =>
              sym = NT "Z" -> False)
      (P0 := fun gamma (pf : nullable_gamma g312 gamma) =>
               In (NT "Z") gamma -> False); intros.
  - crush.
    apply IHnullable_sym; crush.
  - crush.
  - crush.
    + apply IHnullable_sym; auto.
    + apply IHnullable_sym0; auto.
Qed.

Example g312NullableSetCorrect :
  nullable_set_for g312NullableSet g312.
Proof.
Abort. (* to do *)

(* Tests of FIRST set definitions *)

(* FIRST sets for each nonterminal in Grammar 3.12 *)
Definition cSet   := LookaheadSet.add (LA "c") LookaheadSet.empty.
Definition acSet  := LookaheadSet.add (LA "a") cSet.
Definition acdSet := LookaheadSet.add (LA "d") acSet.

(* Correct FIRST set for Grammar 3.12 *)
Definition g312FirstSet :=
  SymbolMap.add
    (NT "X") acSet
    (SymbolMap.add
       (NT "Y") cSet
       (SymbolMap.add
          (NT "Z") acdSet
          (SymbolMap.empty LookaheadSet.t))).

Example c_in_First_Y :
  (@first_sym g312) (LA "c") (NT "Y").
Proof.
  apply FirstNT with (gpre := nil) (y := T "c") (gsuf := nil); crush.
Qed.

Example a_in_First_X :
  (@first_sym g312) (LA "a") (NT "X").
Proof.
  apply FirstNT with (gpre := nil) (y := T "a") (gsuf := nil) ; crush.
Qed.

Example c_in_First_X :
  (@first_sym g312) (LA "c") (NT "X").
Proof.
  apply FirstNT with (gpre := nil) (y := NT "Y") (gsuf := nil); crush.
  apply c_in_First_Y.
Qed.

Example d_not_in_First_Y :
  ~(@first_sym g312) (LA "d") (NT "Y").
Proof.
  unfold not; intros.
  crush.
  crush'.
Qed.

Example d_not_in_First_X :
  ~(@first_sym g312) (LA "d") (NT "X").
Proof.
  unfold not; intros.
  crush.
  crush'.
  - crush'.
  - crush'.
Qed.

Example a_in_First_Z :
  (@first_sym g312) (LA "a") (NT "Z").
Proof.
  apply FirstNT with (gpre := nil) (y := NT "X") (gsuf := [NT "Y"; NT "Z"]); crush.
  apply a_in_First_X.
Qed.

Example c_in_First_Z :
  (@first_sym g312) (LA "c") (NT "Z").
Proof.
  apply FirstNT with (gpre := [NT "X"]) (y := NT "Y") (gsuf := [NT "Z"]); crush.
  - apply X_nullable.
  - apply c_in_First_Y.
Qed.
  
Example d_in_First_Z :
  (@first_sym g312) (LA "d") (NT "Z").
Proof.
  apply FirstNT with (gpre := nil) (y := T "d") (gsuf := nil); crush.
Qed.

Example g312FirstSetCorrect :
  first_set_for g312FirstSet g312.
Proof.
  unfold g312FirstSet.
  unfold first_set_for. split.
  - (* prove that g312FirstSet is complete *)
    unfold first_set_complete; intros.
    revert H.
    induction H0; intros.
    + inv H.
    + crush.
      * crush'.
        exists acdSet; crush.
      * crush'.
        -- crush'.
           crush'.
           exists acdSet; crush.
        -- crush'.
           exists acdSet; crush.
        -- crush'.
           ++ crush'.
              exists acdSet; crush.
           ++ crush'.
              ** apply IHfirst_sym; crush.
              ** apply IHfirst_sym; crush.
      * crush'.
        exists cSet; crush.
      * crush'.
        crush'.
        exists acSet; crush.
      * crush'.
        exists acSet; crush.
  - unfold first_set_minimal; intros.
    copy_and_find_In H.
    crush.
    + apply c_in_First_X.
    + crush'.
      apply a_in_First_X.
    + apply c_in_First_Y.
    + apply c_in_First_Z.
    + crush'.
      * apply a_in_First_Z.
      * crush'.
        apply d_in_First_Z.
Qed.
    
Definition g312FirstSetPlus :=
  SymbolMap.add
    (NT "X") acdSet (* d shouldn't be in there! *)
    (SymbolMap.add
       (NT "Y") cSet
       (SymbolMap.add
          (NT "Z") acdSet
          (SymbolMap.empty LookaheadSet.t))).

Example nonMinimalFirstSetIncorrect :
  ~first_set_for g312FirstSetPlus g312.
Proof.
  unfold not; intros.
  unfold first_set_for in H.
  destruct H as [_ Hmin].
  unfold first_set_minimal in Hmin.
  specialize Hmin with (x := NT "X")
                       (xFirst := acdSet)
                       (la := LA "d").
  assert (H : ~(@first_sym g312) (LA "d") (NT "X")).
  { unfold not; intros.
    crush.
    - crush'.
      crush'.
    - crush'. }
  apply H.
  apply Hmin; crush.
Qed.

Definition Ac_grammar :=
  {| productions := [("A", [NT "A"; T "c"]);
                     ("A", [])];
     start := "A" |}.

Definition Ac_first_set :=
  SymbolMap.add (NT "A") cSet
                (SymbolMap.empty LookaheadSet.t).

(* Got this one using induction on the first_sym derivation *)
Example Ac_first_correct :
  first_set_for Ac_first_set Ac_grammar.
Proof.
  unfold first_set_for.
  split.
  - unfold first_set_complete; intros.
    revert H.
    induction H0; intros.
    + inv H.
    + crush.
      crush'.
      * apply IHfirst_sym; crush.
      * crush'.
        exists cSet; crush.
  - unfold first_set_minimal; intros.
    unfold Ac_first_set in *.
    copy_and_find_In H.
    crush.
    apply FirstNT with (gpre := [NT "A"]) (y := T "c") (gsuf := nil); crush.
    apply NullableSym with (ys := []); crush.
Qed.

(* tests of FOLLOW definitions *)

Definition xFollow := LookaheadSet.add EOF acdSet.
Definition yFollow := LookaheadSet.add EOF acdSet.

(* Correct FOLLOW set for Grammar 3.12 *)
Definition g312FollowSet :=
  SymbolMap.add
    (NT "X") xFollow
    (SymbolMap.add
       (NT "Y") yFollow
       (SymbolMap.empty LookaheadSet.t)).

Example what's_in_xFirst :
  forall la,
    first_sym g312 la (NT "X")
    -> LookaheadSet.In la acSet.
Proof.
  intros.
  pose proof g312FirstSetCorrect as Hc.
  unfold first_set_for in Hc.
  destruct Hc as [Hcom _].
  unfold first_set_complete in Hcom.
  apply Hcom in H; auto.
  destruct H as [xFirst [Hs Hf]].
  inv Hs.
  auto.
Qed.

Example what's_in_yFirst :
  forall la,
    first_sym g312 la (NT "Y")
    -> LookaheadSet.In la cSet.
Proof.
  intros.
  pose proof g312FirstSetCorrect as Hc.
  unfold first_set_for in Hc.
  destruct Hc as [Hcom _].
  unfold first_set_complete in Hcom.
  apply Hcom in H; auto.
  destruct H as [yFirst [Hs Hf]].
  inv Hs.
  auto.
Qed.

Example what's_in_zFirst :
  forall la,
    first_sym g312 la (NT "Z")
    -> LookaheadSet.In la acdSet.
Proof.
  intros.
  pose proof g312FirstSetCorrect as Hc.
  unfold first_set_for in Hc.
  destruct Hc as [Hcom _].
  unfold first_set_complete in Hcom.
  apply Hcom in H; auto.
  destruct H as [zFirst [Hs Hf]].
  inv Hs.
  auto.
Qed.

(* Another possible approach -- use the "what's in xFirst"
   strategy for the other cases *)
Example finiteFollowCorrect :
  follow_set_for g312FollowSet g312.
Proof.
  unfold follow_set_for. split.
  - unfold follow_set_complete; intros.
    induction H.
    + induction H. 
      crush.
      * pose proof Z_not_nullable as Hz.
        apply Hz in H3.
        congruence.
      * exists yFollow; crush.
      * exists xFollow; crush.
    + crush.
      * crush'.
      * crush'.
        -- inv H0.
           destruct gpre.
           ++ inv H.
              apply what's_in_yFirst in H3.
              crush.
              exists xFollow; crush.
           ++ inv H.
              destruct gpre.
              ** inv H4.
                 apply what's_in_zFirst in H3.
                 crush.
                 --- exists xFollow; crush.
                 --- inv H0.
                     +++ exists xFollow; crush.
                     +++ inv H1.
                         *** exists xFollow; crush.
                         *** inv H0.
              ** crush.
                 inv H4.
                 symmetry in H5; crush.
        -- crush'.
           ++ inv H0.
              destruct gpre.
              ** inv H.
                 apply what's_in_zFirst in H3.
                 crush.
                 --- exists yFollow; crush.
                 --- inv H0.
                     +++ exists yFollow; crush.
                     +++ inv H2.
                         *** exists yFollow; crush.
                         *** inv H0.
              ** inv H.
                 symmetry in H4; crush.
           ++ crush'.
              inv H0.
              symmetry in H; crush.
      * crush'.
      * crush'.
        inv H0.
        symmetry in H; crush.
      * crush'.
    + crush.
      * crush'.
      * crush'.
        -- pose proof Z_not_nullable.
           apply H in H2; congruence.
        -- destruct IHfollow_sym as [zFollow [Hs Hl]].
           inv Hs.
      * crush'.
      * crush'.
        destruct IHfollow_sym as [xFollow [Hs Hl]].
        inv Hs.
        crush.
        -- exists yFollow; crush.
        -- inv H2.
           ++ exists yFollow; crush.
           ++ inv H3.
              ** exists yFollow; crush.
              ** inv H2.
                 --- exists yFollow; crush.
                 --- inv H3.
      * crush'.
  - unfold follow_set_minimal; intros.
    unfold g312FollowSet in *.
    copy_and_find_In H.
    crush.
    (* make these separate examples *)
    + apply FollowRight with (x1 := "Z")
                             (gpre := nil)
                             (gsuf := [NT "Y"; NT "Z"]); crush.
      apply FirstGamma with (gpre := nil)
                            (y := NT "Y"); crush.
      apply c_in_First_Y.
    + inv H1.
      * apply FollowRight with (x1 := "Z")
                               (gpre := nil)
                               (gsuf := [NT "Y"; NT "Z"]); crush.
        apply FirstGamma with (gpre := [NT "Y"]).
        -- constructor; crush.
           apply Y_nullable.
        -- apply a_in_First_Z.
      * inv H0.
        -- apply FollowRight with (x1 := "Z")
                                  (gpre := nil)
                                  (gsuf := [NT "Y"; NT "Z"]); crush.
           ++ apply FirstGamma with (gpre := [NT "Y"]).
              ** constructor; crush.
                 apply Y_nullable.
              ** apply d_in_First_Z.
        -- inv H1.
           ++ apply FollowNullable.
              apply X_nullable.
           ++ inv H0.
    + apply FollowRight with (x1 := "Z")
                             (gpre := [NT "X"])
                             (gsuf := [NT "Z"]); crush.
      apply FirstGamma with (gpre := nil); crush.
      apply c_in_First_Z.
    + inv H1.
      * apply FollowRight with (x1 := "Z")
                               (gpre := [NT "X"])
                               (gsuf := [NT "Z"]); crush.
        apply FirstGamma with (gpre := nil); crush.
        apply a_in_First_Z.
      * inv H0.
        -- apply FollowRight with (x1 := "Z")
                                  (gpre := [NT "X"])
                                  (gsuf := [NT "Z"]); crush.
           apply FirstGamma with (gpre := nil); crush.
           apply d_in_First_Z.
        -- inv H1.
           ++ apply FollowNullable.
              apply Y_nullable.
           ++ inv H0.
Qed. (* got it! *)

(* The next tests use Grammar 3.11, shown here:

   S -> if E then S else S
   S -> begin S L
   S -> print E

   L -> end
   L -> ; S L

   E -> num = num

 *)

(* Fix the nonterminal and terminal types, and their
   corresponding modules, before filling out this example *)
Example g311ParseTableCorrect :
  parse_table_for g311ParseTable g311.
Proof.
Abort.
