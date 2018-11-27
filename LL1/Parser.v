Require Import FMaps List MSets String.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Utils.
Require Import Lib.Tactics.
Require Import LL1.ParseTable. 
Import ListNotations.
Open Scope string_scope.

Definition peek input :=
  match input with
  | nil => EOF
  | token :: _ => LA token
  end.

(* fuel-based parser *)

Fixpoint parse (tbl : parse_table)
         (sym : symbol)
         (input : list string)
         (fuel : nat) : (option tree * list string) :=
  match fuel with
  | O => (None, input)
  | S n => 
    match (sym, input) with
    | (T y, nil) => (None, input)
    | (T y, token :: input') =>
      match beqString y token with
      | false => (None, input)
      | true => (Some (Leaf y), input')
      end
    | (NT x, _) =>
      match pt_lookup x (peek input) tbl with
      | None => (None, input)
      | Some gamma =>
        match parseForest tbl gamma input n with
        | (None, _) => (None, input)
        | (Some sts, input') =>
          (Some (Node x sts), input')
        end
      end
    end
  end
with parseForest (tbl : parse_table) 
                 (gamma : list symbol)
                 (input : list string)
                 (fuel : nat) :
       (option (list tree) * list string) :=
       match fuel with
       | O => (None, input)
       | S n =>
         match gamma with
         | nil => (Some nil, input)
         | sym :: gamma' =>
           match parse tbl sym input n with
           | (None, _) => (None, input)
           | (Some lSib, input') =>
             match parseForest tbl gamma' input' n with
             | (None, _) => (None, input)
             | (Some rSibs, input'') =>
               (Some (lSib :: rSibs), input'')
             end
           end
         end
       end.

(* fuel-less implementation *)

Section Lexicographic.

Variables (A B : Type) (leA : relation A) (leB : relation B).

Inductive lexprod : A * B -> A * B -> Prop :=
| left_lex  : forall x x' y y', leA x x' -> lexprod (x, y) (x', y')
| right_lex : forall x y y',    leB y y' -> lexprod (x, y) (x, y').

Theorem lexprod_trans :
  transitive _ leA
  -> transitive _ leB
  -> transitive _ lexprod.
Proof.
  intros tA tB [x1 y1] [x2 y2] [x3 y3] H12 H23.
  inv H12; inv H23.
  - apply left_lex; eauto.
  - apply left_lex; auto.
  - apply left_lex; auto.
  - apply right_lex; eauto.
Qed.

Theorem lexprod_wf :
  well_founded leA
  -> well_founded leB
  -> well_founded lexprod.
Proof.
  intros wfA wfB (x, y).
  revert y.
  induction (wfA x) as [x _ IHx].
  intros y.
  induction (wfB y) as [y _ IHy].
  constructor.
  intros (x', y') H.
  inv H; eauto.
Qed.

End Lexicographic.

Require Import Coq.Arith.Wf_nat.

Definition nat_lexprod : relation (nat * nat) :=
  lexprod nat nat lt lt.

Lemma nat_lexprod_wf : well_founded nat_lexprod.
Proof.
  apply lexprod_wf; apply lt_wf.
Qed.

