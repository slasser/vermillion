Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Program.Wf.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.

(* Compute the NULLABLE set for a grammar *)

Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
  end.

Definition updateNu (p : production) (nu : NtSet.t) :=
  let (x, gamma) := p in
  if nullableGamma gamma nu then
    NtSet.add x nu
  else
    nu.

Definition nullablePass ps nu :=
  fold_right updateNu nu ps.

(* Incomplete attempt to write mkNullableSet without fuel *)

Definition card_order (s1 s2 : NtSet.t) := 
  NtSet.cardinal s1 < NtSet.cardinal s2.

Lemma card_order_wf' : 
  forall n s, 
    NtSet.cardinal s <= n
    -> Acc card_order s.
Proof.
  induction n as [| n]; intros s Hle; constructor;
  intros s2 Hco; unfold card_order in Hco; try omega.
  apply IHn; omega.
Defined.

Lemma card_order_wf : well_founded card_order.
Proof.
  unfold well_founded; intros s.
  eapply card_order_wf'; eauto.
Defined.

(* This isn't quite right -- we can prove that nu' is larger 
   than nu for all recursive calls, but we need to show that 
   the set difference (all grammar nonterminals - nu') is 
   getting smaller. *) 
Definition mkNullableSet (ps : list production) : NtSet.t.
  refine (let iter := Fix card_order_wf
                            (fun _ => _)
                            (fun (nu : NtSet.t)
                                 (iter : forall nu', card_order nu' nu -> NtSet.t) =>
                               let nu' := nullablePass ps nu in
                               if NtSet.eq_dec nu nu' then
                                 nu'
                               else
                                 iter nu' _)
          in  iter NtSet.empty).
Abort.

(* Another attempt at a fuel-less mkNullableSet,
   this time with a different order *)

Definition diff_order (s1 s2 s3 : NtSet.t) := 
  NtSet.cardinal (NtSet.diff s1 s2) < NtSet.cardinal (NtSet.diff s1 s3).

Lemma diff_order_wf' : 
  forall n s1 s2, 
    NtSet.cardinal (NtSet.diff s1 s2) <= n
    -> Acc (diff_order s1) s2.
Proof.
  induction n as [| n]; intros s1 s2 Hle; constructor;
  intros s3 Hdo; unfold diff_order in Hdo; try omega.
  apply IHn; omega.
Defined.

Lemma diff_order_wf :
  forall s1, well_founded (diff_order s1).
Proof.
  intros s1.
  unfold well_founded; intros s2.
  eapply diff_order_wf'; eauto.
Defined.

Definition ntSetFromList (ls : list nonterminal) :=
  fold_right NtSet.add NtSet.empty ls.

Definition lhSet (ps : list production) :=
  ntSetFromList (map fst ps).

(* Better, but we still don't have any information about the
   relationship between (lhSet ps) and nu in the proof context *)
Definition mkNullableSet (ps : list production) : NtSet.t.
  refine (let init := NtSet.empty in
          let iter := Fix (diff_order_wf (lhSet ps))
                          (fun _ => _)
                          (fun (nu : NtSet.t)
                               (iter : forall nu', diff_order (lhSet ps) nu' nu -> NtSet.t) =>
                             let nu' := nullablePass ps nu in
                             if NtSet.eq_dec nu nu' then
                               nu'
                             else
                               iter nu' _) in
          iter init).
  simpl in *.
Abort.

(*
Lemma nullablePass_le :
  forall ps nu nu',
    nu' = nullablePass ps nu
    -> NtSet.Equal nu nu'
       \/ NtSet.cardinal nu < NtSet.cardinal nu'.
Proof.
  induction ps as [| p ps]; intros nu nu' Heq; simpl in *; subst.
  - left.
    apply NtSetEqProps.MP.equal_refl.
  - destruct (IHps nu (nullablePass ps nu)); auto.
    + (* nu wasn't changed by any of the latter productions *)
      pose proof updateNu_le as Hun.
      destruct (Hun p (nullablePass ps nu) (updateNu p (nullablePass ps nu))); auto.
      * left.
        apply NtSetEqProps.MP.equal_trans with
            (s2 := nullablePass ps nu); auto.
      * right.
        apply NtSetEqProps.MP.Equal_cardinal in H.
        omega.
    + pose proof updateNu_le as Hun.
      destruct (Hun p (nullablePass ps nu) (updateNu p (nullablePass ps nu))); auto.
      * apply NtSetEqProps.MP.Equal_cardinal in H0.
        right.
        omega.
      * right; omega.
Qed.      
*)

(* New thing : the intersection part *)
Definition nullableMeasure (ps : list production) (nu : NtSet.t) :=
  let candidates := lhSet ps in
  NtSet.cardinal (NtSet.diff candidates nu).

Import MSetDecide.
Module Import NSD := WDecideOn NT_as_DT NtSet.

Lemma cardinal_gt_iff_lt :
  forall s1 s2,
    NtSet.cardinal s1 < NtSet.cardinal s2
    <-> NtSet.cardinal s2 > NtSet.cardinal s1.
Proof.
  split; intros; omega.
Qed.

Module MP := MSetProperties.Properties NtSet.

Lemma subset_subset_diffs :
  forall a b c : NtSet.t,
    NtSet.Subset a b
    -> NtSet.Subset (NtSet.diff c b) (NtSet.diff c a).
Proof.
  intros a b c Hsub; fsetdec.
Qed.

Lemma subset_subset_inters :
  forall a b c : NtSet.t,
    NtSet.Subset a b
    -> NtSet.Subset (NtSet.inter c a) (NtSet.inter c b).
Proof.
  fsetdec.
Qed.

Lemma in_nin_diff :
  forall x s1 s2,
    NtSet.In x s2
    -> ~ NtSet.In x s1
    -> NtSet.In x (NtSet.diff s2 s1).
Proof.
  fsetdec.
Qed.

Lemma nin_nin_inter :
  forall x a b,
    ~ NtSet.In x b
    -> ~ NtSet.In x (NtSet.inter a b).
Proof.
  fsetdec.
Qed.

Lemma nullablePass_subset :
  forall ps nu,
    NtSet.Subset nu (nullablePass ps nu).
Proof.
  induction ps as [| p ps]; intros nu; simpl in *.
  - apply NtSetEqProps.MP.subset_refl.
  - unfold updateNu.
    destruct p as (x, gamma).
    destruct (nullableGamma gamma (nullablePass ps nu)); auto.
    apply MP.subset_add_2; auto.
Qed.

Lemma In_lhSet_cons :
  forall x' ps x gamma,
    NtSet.In x' (lhSet ps)
    -> NtSet.In x' (lhSet ((x, gamma) :: ps)).
Proof.
  intros.
  unfold lhSet in *; simpl in *.
  apply F.add_2; auto.
Qed.

Lemma nullablePass_eq_or_exists :
  forall ps nu,
    NtSet.Equal nu (nullablePass ps nu)
    \/ exists x,
      NtSet.In x (lhSet ps)
      /\ ~NtSet.In x nu
      /\ NtSet.In x (nullablePass ps nu).
Proof.
  induction ps as [| p ps]; intros nu; simpl in *.
  - left.
    apply MP.equal_refl.
  - unfold updateNu.
    destruct p as (x, gamma).
    destruct (nullableGamma gamma (nullablePass ps nu)).
    + (* gamma is nullable -- add x *)
      destruct (NtSetEqProps.MP.In_dec x nu).
      * destruct (IHps nu).
        -- left; fsetdec.
        -- right.
           destruct H as [x' [Hin [Hnin Hin']]].
           exists x'; repeat split; auto.
           ++ apply In_lhSet_cons; auto.
           ++ apply F.add_2; auto.
      * right.
        exists x; repeat split; auto.
        -- unfold lhSet; simpl.
           apply F.add_1; auto.
        -- apply F.add_1; auto.
    + destruct (IHps nu); auto.
      destruct H as [x' [Hin [Hnin Hin']]].
      right.
      exists x'; split; auto.
      apply In_lhSet_cons; auto.
Qed.
      
(* NtSetEqProps.MP.diff_inter_cardinal *)
Program Fixpoint mkNullableSet' (ps : list production) 
        (nu : NtSet.t)
        { measure (nullableMeasure ps nu) }:=
  let nu' := nullablePass ps nu in
  if NtSet.eq_dec nu nu' then
    Some nu
  else
    mkNullableSet' ps nu'.
Next Obligation.
  unfold nullableMeasure.
  pose proof (nullablePass_eq_or_exists ps nu) as Hnp.
  destruct Hnp as [Heq | Hex].
  - unfold NtSet.eq in H; congruence.
  - destruct Hex as [x [Hin [Hnin Hin']]].
    apply NtSetEqProps.MP.subset_cardinal_lt with (x := x); try fsetdec.
    apply subset_subset_diffs.
    apply nullablePass_subset.
Defined.

(* Give up and define mkNullableSet with a fuel argument *)
Fixpoint mkNullableSet'' (ps : list production) (nu : NtSet.t) (fuel : nat) : option NtSet.t :=
  match fuel with
  | O => None
  | S n' =>
    let nu' := nullablePass ps nu in
    if NtSet.eq_dec nu nu' then
      Some nu'
    else 
      mkNullableSet'' ps nu' n'
  end.

Definition mkNullableSet_with_fuel (g : grammar) :=
  mkNullableSet'' (productions g)
                  NtSet.empty
                  (NtSet.cardinal (lhSet (productions g))).

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition table_entry := (nonterminal * lookahead * list symbol)%type.

Lemma table_entry_dec :
  forall e e2 : table_entry,
    {e = e2} + {e <> e2}.
Proof.
  repeat decide equality.
Defined.

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition fromLookaheadList x gamma las : list table_entry :=
  map (fun la => (x, la, gamma)) las.

Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :
  list lookahead :=
  match gamma with 
  | [] => []
  | T y :: _ => [LA y]
  | NT x :: gamma' => 
    let xFirst := match NtMap.find x fi with
                  | Some s => LaSet.elements s
                  | None => []
                  end
    in  if NtSet.mem x nu then xFirst ++ firstGamma gamma' nu fi else xFirst
  end.

Definition firstEntries x gamma nu fi :=
  fromLookaheadList x gamma (firstGamma gamma nu fi).

Definition followLookahead x gamma nu fo :=
  if nullableGamma gamma nu then
    match NtMap.find x fo with 
    | Some s => LaSet.elements s
    | None => []
    end
  else 
    [].

Definition followEntries x gamma nu fo :=
  fromLookaheadList x gamma (followLookahead x gamma nu fo).

Definition entriesForProd nu fi fo (prod : production) : list table_entry :=
  let (x, gamma) := prod in
  firstEntries x gamma nu fi ++ followEntries x gamma nu fo.

Definition tableEntries' nu fi fo ps :=
  flat_map (entriesForProd nu fi fo) ps.

Definition tableEntries nu fi fo g :=
  tableEntries' nu fi fo g.(productions).

(* Build a parse table from a (correct) list of parse table entries *)

Definition empty_table := ParseTable.empty (list symbol).

Definition addEntry (p : table_entry) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | (x, la, gamma) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition tableFromEntries (ps : list table_entry) : option parse_table :=
  fold_right addEntry (Some empty_table) ps.

(* Combining all of the steps into a single function *)
(* The type of this function will change as I add code for computing NULLABLE, etc. *)

Definition mkParseTable g nu fi fo :=
  let es := tableEntries nu fi fo g in
  tableFromEntries es.
  

