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

Inductive parse_result (A : Type) : Type :=
| Succ : (A * list string * list nonterminal) -> parse_result A
| Fail : (string * list string) -> parse_result A
| LRec : list nonterminal -> parse_result A.

Inductive sym_input : Set :=
| parse_input : symbol -> sym_input
| parseForest_input : list symbol -> sym_input.

Definition parse_type (sin : sym_input) : Type :=
  match sin with
  | parse_input _ => parse_result tree
  | parseForest_input _ => parse_result (list tree)
  end.

Require Import Program.Wf.

Definition parse_measure (word : list string) (tbl : parse_table) (visited : list nonterminal) :=
  (List.length word, List.length word).

Program Fixpoint parse' (tbl     : parse_table)
                        (sym_in  : sym_input)
                        (word    : list string)
                        (visited : list nonterminal)
                       {measure (parse_measure word tbl visited) (nat_lexprod)}
                       : parse_type sym_in := 
  match sym_in with
  | parse_input sym =>
    (* morally, a call to parse *)
    match (sym, word) with
    | (T y, nil) => Fail tree ("error message", word)
    | (T y, token :: word') =>
      match beqString y token with
      | false => Fail tree ("error message", word)
      | true => Succ tree (Leaf y, word', nil)
      end
    | (NT x, _) =>
      if List.in_dec NT_as_DT.eq_dec x visited then
        LRec tree (x :: visited)
      else
        match pt_lookup x (peek word) tbl with
        | None => Fail tree ("error message", word)
        | Some gamma =>
          match parse' tbl (parseForest_input gamma) word (x :: visited) with
          | LRec _ cycle => LRec tree cycle
          | Fail _ pr => Fail tree pr
          | Succ _ (sts, word', visited') => Succ tree (Node x sts, word', visited')
          end
        end
    end
  | parseForest_input gamma =>
    match gamma with
    | nil => Succ (list tree) (nil, word, visited)
    | sym :: gamma' =>
      match parse' tbl (parse_input sym) word visited with
      | LRec _ cycle => LRec (list tree) cycle
      | Fail _ pr => Fail (list tree) pr
      | Succ _ (lSib, word', visited') =>
        match parse' tbl (parseForest_input gamma') word' visited' with
        | LRec _ cycle => LRec (list tree) cycle
        | Fail _ pr => Fail (list tree) pr
        | Succ _ (rSibs, word'', visited'') =>
          Succ (list tree) (lSib :: rSibs, word'', visited'')
        end
      end
    end
  end.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Extraction parse'.
