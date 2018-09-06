Require Import List.

Require Import Program.Wf.

Require Import Lib.Grammar.
Require Import Lib.Tactics.

Require Import LL1.ParseTable.

Import ListNotations.
Import MSetDecide.

Module Import NtSetDecide := WDecideOn NT_as_DT NtSet.

(* Step 1: compute the NULLABLE set for a grammar *)

Definition fromNtList (ls : list nonterminal) : NtSet.t :=
  fold_right NtSet.add NtSet.empty ls.

Definition lhSet (ps : list production) : NtSet.t :=
  fromNtList (map fst ps).

Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
  end.

Definition updateNu (p : production) (nu : NtSet.t) : NtSet.t :=
  let (x, gamma) := p in
  if nullableGamma gamma nu then
    NtSet.add x nu
  else
    nu.

Definition nullablePass (ps : list production) (nu : NtSet.t) : NtSet.t :=
  fold_right updateNu nu ps.

Lemma subset_subset_diffs :
  forall a b c : NtSet.t,
    NtSet.Subset a b
    -> NtSet.Subset (NtSet.diff c b) (NtSet.diff c a).
Proof.
  fsetdec.
Qed.

Lemma nullablePass_subset :
  forall ps nu,
    NtSet.Subset nu (nullablePass ps nu).
Proof.
  induction ps as [| p ps]; intros nu; simpl in *; try fsetdec.
  unfold updateNu.
  destruct p as (x, gamma).
  destruct (nullableGamma gamma (nullablePass ps nu)); auto.
  apply NtSetEqProps.MP.subset_add_2; auto.
Qed.

Lemma In_lhSet_cons :
  forall x' ps x gamma,
    NtSet.In x' (lhSet ps)
    -> NtSet.In x' (lhSet ((x, gamma) :: ps)).
Proof.
  intros.
  unfold lhSet in *; simpl in *; fsetdec.
Qed.

Lemma nullablePass_eq_or_exists :
  forall ps nu,
    NtSet.Equal nu (nullablePass ps nu)
    \/ exists x,
      NtSet.In x (lhSet ps)
      /\ ~NtSet.In x nu
      /\ NtSet.In x (nullablePass ps nu).
Proof.
  induction ps as [| p ps]; intros nu; simpl in *; try fsetdec.
  unfold updateNu.
  destruct p as (x, gamma).
  destruct (nullableGamma gamma (nullablePass ps nu)).
  - destruct (NtSetEqProps.MP.In_dec x nu).
    + destruct (IHps nu).
      * left; fsetdec.
      * destruct H as [x' [Hin [Hnin Hin']]].
        right; eexists; repeat split; eauto.
        -- apply In_lhSet_cons; auto.
        -- fsetdec.
    + right; eexists; repeat split; eauto; try fsetdec.
      unfold lhSet; simpl; fsetdec.
  - destruct (IHps nu); auto.
    destruct H as [x' [Hin [Hnin Hin']]].
    right; eexists; split; eauto.
    apply In_lhSet_cons; auto.
Qed.

Lemma nullablePass_neq_exists :
  forall ps nu,
    ~ NtSet.Equal nu (nullablePass ps nu)
    -> exists x,
      NtSet.In x (lhSet ps)
      /\ ~ NtSet.In x nu
      /\ NtSet.In x (nullablePass ps nu).
Proof.
  intros ps nu Hneq.
  destruct (nullablePass_eq_or_exists ps nu); congruence.
Qed.

Definition numRemainingCandidates (ps : list production) (nu : NtSet.t) : nat :=
  let candidates := lhSet ps in
  NtSet.cardinal (NtSet.diff candidates nu).

Lemma nullablePass_neq_candidates_lt :
  forall ps nu,
    ~ NtSet.Equal nu (nullablePass ps nu)
    -> numRemainingCandidates ps (nullablePass ps nu) < numRemainingCandidates ps nu.
Proof.
  intros ps nu Hneq.
  apply nullablePass_neq_exists in Hneq.
  firstorder.
  apply NtSetEqProps.MP.subset_cardinal_lt with (x := x); try fsetdec.
  apply subset_subset_diffs.
  apply nullablePass_subset.
Qed.
  
Program Fixpoint mkNullableSet' 
        (ps : list production) 
        (nu : NtSet.t)
        { measure (numRemainingCandidates ps nu) }:=
  let nu' := nullablePass ps nu in
  if NtSet.eq_dec nu nu' then
    nu
  else
    mkNullableSet' ps nu'.
Next Obligation.
  apply nullablePass_neq_candidates_lt; auto.
Defined.

Definition mkNullableSet (g : grammar) : NtSet.t :=
  mkNullableSet' g.(productions) NtSet.empty.

(* Step 4 : build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition table_entry := (nonterminal * lookahead * list symbol)%type.

Lemma table_entry_dec :
  forall e e2 : table_entry,
    {e = e2} + {e <> e2}.
Proof.
  repeat decide equality.
Defined.

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

Definition mkEntries' nu fi fo ps :=
  flat_map (entriesForProd nu fi fo) ps.

Definition mkEntries nu fi fo g :=
  mkEntries' nu fi fo g.(productions).

(* Step 5 : build a parse table from a (correct) list of parse table entries *)

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

Definition mkParseTable (ps : list table_entry) : option parse_table :=
  fold_right addEntry (Some empty_table) ps.

(* Combining all of the steps into a single function *)
(* The type of this function will change as I add code for computing NULLABLE, etc. *)

Definition genTableForGrammar g nu fi fo :=
  let es := mkEntries nu fi fo g in
  mkParseTable es.

