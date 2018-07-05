Require Import List.
Require Import MSets.
Require Import String.

Require Import Lib.ExampleGrammars.
Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.Lemmas.
Require Import LL1.ParseTable.

Import ListNotations.

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
  (SymbolSet.add
     (NT "X")
     (SymbolSet.add
        (NT "Y")
        SymbolSet.empty)).

Example Y_nullable :
  (@nullable_sym g312) (NT "Y").
Proof. crush. Qed.

Example X_nullable :
  (@nullable_sym g312) (NT "X").
Proof. crush. Qed.

(* We can't prove this false statement, which is good *)
Example Z_nullable :
  (@nullable_sym g312) (NT "Z").
Proof. crush. Abort.

Example Z_nullable :
  (@nullable_sym g312) (NT "Z").
Proof. 
  econstructor.
  eapply NuProd with (ys := [NT "X"; NT "Y"; NT "Z"]).
  - crush.
  - constructor.
    + apply X_nullable.
    + constructor.
      * apply Y_nullable.
      * constructor.
        -- (* back where we started *)
Abort.

(* With the current definitions, though, we can't immediately
   prove that a particular symbol ISN'T nullable *)
Example Z_not_nullable :
  ~(@nullable_sym g312) (NT "Z").
Proof.
  unfold not. intros.
  inv H. inv H0. crush.
Abort.

(* Let's try again using the nullable_nonrec lemma *)
Example Z_not_nullable :
  ~(@nullable_sym g312) (NT "Z").
Proof.
  unfold not; intros.
  apply nullable_nonrec in H.
  destruct H as [gamma].
  destruct H.
  inv H.
  crush.
  apply H0; crush.
Qed.

(* The previous lemma allows us to get through this one, too *)
Example g312NullableSetCorrect :
  nullable_set_for g312NullableSet g312.
Proof.
  unfold nullable_set_for. split.
  - unfold nullable_set_complete; intros.
    inv H.
    crush.
    exfalso.
    apply Z_not_nullable; auto.
  - unfold nullable_set_minimal; intros.
    crush.
Qed.    

(* We can prove that an incomplete nullable set is  incorrect *)
Example incompleteNullableSetIncorrect :
  ~nullable_set_for (SymbolSet.singleton (NT "X")) g312.
Proof.
  unfold not; intros.
  inv H.
  clear H1.
  unfold nullable_set_complete in H0.
  pose proof Y_nullable.
  apply H0 in H.
  crush.
Qed.


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
  apply FiNT with (gamma := [T "c"]); crush.
Qed.

Example a_in_First_X :
  (@first_sym g312) (LA "a") (NT "X").
Proof.
  apply FiNT with (gamma := [T "a"]); crush.
Qed.

Example c_in_First_X :
  (@first_sym g312) (LA "c") (NT "X").
Proof.
  apply FiNT with (gamma := [NT "Y"]); crush.
  apply FiGammaHd.
  econstructor.
  apply FiProd with (gamma := [T "c"]); crush.
Qed.

Example d_not_in_First_Y :
  ~(@first_sym g312) (LA "d") (NT "Y").
Proof.
  unfold not; intros.
  crush.
Qed.

Example d_not_in_First_X :
  ~(@first_sym g312) (LA "d") (NT "X").
Proof.
  unfold not; intros.
  crush.
Qed.

Example a_in_First_Z :
  (@first_sym g312) (LA "a") (NT "Z").
Proof.
  apply FiNT with (gamma := [NT "X"; NT "Y"; NT "Z"]);
  crush.
  apply FiGammaHd.
  apply FiNT with (gamma := [T "a"]).
  crush.
Qed.

Example c_in_First_Z :
  (@first_sym g312) (LA "c") (NT "Z").
Proof.
  apply FiNT with (gamma := [NT "X"; NT "Y"; NT "Z"]); crush.
  apply FiGammaTl.
  - apply X_nullable.
  - apply FiGammaHd.
    apply FiNT with (gamma := [T "c"]).
    crush.
Qed.
  
Example d_in_First_Z :
  (@first_sym g312) (LA "d") (NT "Z").
Proof.
  apply FiNT with (gamma := [T "d"]); crush.
Qed.


Example g312FirstSetCorrect :
  first_set_for g312FirstSet g312.
Proof.
  unfold g312FirstSet.
  unfold first_set_for. split.
  - unfold first_set_complete; intros.
    inv H0; crush.
    + exists acdSet.
      crush.
    + exists acdSet. split.
      * crush.
      * inv H2.
        -- inv H3.
           crush.
        -- inv H5.
           ++ crush.
           ++ inv H6.
              **(* We're getting stuck in a loop because of the
                   Z here. *)
                inv H2.
                 inv H0.
                 inv H2.
                 --- inv H0.
                     crush.
                 --- inv H0.
                     +++ inv H1.
Abort.

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
  { unfold not; intros; crush. }
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

Example Ac_first_correct :
  first_set_for Ac_first_set Ac_grammar.
Proof.
  unfold first_set_for.
  split.
  - unfold first_set_complete.
    intros.
    revert H.
    induction H0 using first_sym_mutual_ind with
        (P := fun la x gamma (pf : first_prod la x gamma) =>
                Utils.isNT x = true
                -> exists xFirst : LookaheadSet.t,
                  SymbolMap.find (elt:=LookaheadSet.t) x Ac_first_set = Some xFirst /\ LookaheadSet.In la xFirst)
        (P0 := fun la gamma (pf : first_gamma la gamma) =>
                 forall gpre y gsuf,
                   gamma = gpre ++ y :: gsuf
                   -> nullable_gamma gpre
                   -> first_sym la y
                   -> exists yFirst : LookaheadSet.t,
                       SymbolMap.find (elt:=LookaheadSet.t) y Ac_first_set = Some yFirst /\ LookaheadSet.In la yFirst).

    + intros.
      inv i.
      * admit.
      * inv H0.
        -- inv H1.
           inv f.
        -- inv H1.
Abort.

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

Example finiteFollowCorrect :
  follow_set_for g312FollowSet g312.
Proof.
  unfold follow_set_for. split.
  - unfold follow_set_complete; intros.
    inv H.
    + crush.
      * exfalso.
        apply Z_not_nullable.
        auto.
      * exists xFollow. crush.
      * exists xFollow. crush.
    + crush.
      * inv H1.
        -- crush.
           exists xFollow. crush.
        -- inv H4.
           ++ crush.
              ** exists xFollow. crush.
              ** inv H4.
                 (* We're going to get caught in a loop here
                    because of the first_gamma definition *)
Abort.


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
