Require Import FMaps List MSets String.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Utils.
Require Import Lib.Tactics.
Require Import LL1.ParseTable. 
Require Import LL1.ParseTableGen. (* for fromNtList *)
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

Inductive lexprod : A * B  -> A * B -> Prop :=
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

(*
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


(* based on Yves Bertot's suggestion for combining two mutually recursive functions
   into a single function. Doesn't work, because there's not enough information in
   the hypotheses to prove the generated goals. *)
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


Inductive parse_failure : Set :=
| Error    : parse_failure
| Mismatch : string -> list string -> parse_failure
| LeftRec  : list nonterminal -> parse_failure.
*)


(* Tried doing structural induction on the Acc proof, but don't know how yet *)
(*
Lemma foo :
  forall input input' tbl tbl' visited visited',
    nat_lexprod (parse_measure input tbl visited) (parse_measure input' tbl' visited').
Admitted.

Fixpoint parse'' (tbl : parse_table)
                 (sym : symbol)
                 (input : list string)
                 (visited : list nonterminal)
                 (acc : Acc nat_lexprod (parse_measure input tbl visited))
                 : either :=
  match (sym, input) with
  | (T y, nil) => Left (Mismatch "error mesage" input)
  | (T y, token :: input') =>
    match beqString y token with
    | false => Left (Mismatch "error message" input)
    | true =>  Right (Leaf y, input', nil)
    end
  | (NT x, _) =>
    match pt_lookup x (peek input) tbl with
    | None => Left (Mismatch "error message" input)
    | Some gamma =>
      match parseForest'' tbl gamma input (x :: visited) (foo input input tbl tbl visited (x :: visited)) with
      | Left pf => Left pf
      | Right (sts, input', visited') => Right (Node x sts, input', visited')
      end
    end
  end
with parseForest'' (tbl : parse_table) 
                   (gamma : list symbol)
                   (input : list string)
                   (visited : list nonterminal)
                   (acc : Acc nat_lexprod (parse_measure input tbl visited))
                   : either :=
       match gamma with
       | nil => Right (nil, input, visited)
       | sym :: gamma' =>
         match parse'' tbl sym input visited (foo input input tbl tbl visited visited) with
           | Left pf => Left pf
           | Right (lSib, input', visited') =>
             match parseForest'' tbl gamma' input' visited' with
             | Left pf => Left pf
             | Right (rSibs, input'', visited'') =>
               Right (lSib :: rSibs, input'', visited'')
             end
         end
       end.
end.
*)

Definition sym_input : Type := sum (list symbol) symbol.
Definition sem_value : Type := sum (list tree) tree.

Inductive parse_failure : Set :=
| Mismatch : string -> list string -> parse_failure
| LeftRec  : list nonterminal -> parse_failure
| Error    : parse_failure.

(*
Fixpoint nt_keys (tbl : parse_table) : list nonterminal :=
  List.map (fun pr => match pr with 
                      | ((x, _), _) => x
                      end)
           (ParseTable.elements tbl).
 *)

(*
Definition parse_measure (word : list string) (tbl : parse_table) (visited : list nonterminal) :=
  (List.length word, NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))
                                                (fromNtList visited))).
*)
Require Import Program.Wf.

Lemma in_A_not_in_B_in_diff :
  forall elt a b,
    NtSet.In elt a
    -> ~ NtSet.In elt b
    -> NtSet.In elt (NtSet.diff a b).
Proof.
  ND.fsetdec.
Defined.

Lemma in_list_iff_in_fromNtList :
  forall x l, In x l <-> NtSet.In x (fromNtList l).
Proof.
  split; intros; induction l; simpl in *.
  - inv H.
  - destruct H; subst; auto.
    + ND.fsetdec.
    + apply IHl in H; ND.fsetdec.
  - ND.fsetdec.
  - destruct (NtSetFacts.eq_dec x a); subst; auto.
    right. apply IHl. ND.fsetdec.
Defined.

Lemma pt_lookup_elements' :
  forall (k : ParseTable.key) (gamma : list symbol) (l : list (ParseTable.key * list symbol)),
    findA (ParseTableFacts.eqb k) l = Some gamma
    -> In (k, gamma) l.
Proof.
  intros.
  induction l.
  - inv H.
  - simpl in *.
    destruct a as (k', gamma').
    destruct (ParseTableFacts.eqb k k') eqn:Heq.
    + inv H.
      unfold ParseTableFacts.eqb in *.
      destruct (ParseTableFacts.eq_dec k k').
      * subst; auto.
      * inv Heq.
    + right; auto.
Qed.
      
Lemma pt_lookup_elements :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> In ((x, la), gamma) (ParseTable.elements tbl).
Proof.
  intros.
  unfold pt_lookup in *.
  rewrite ParseTableFacts.elements_o in H.
  apply pt_lookup_elements'; auto.
Qed.

(*
Lemma pt_lookup_in_tbl :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> In x (nt_keys tbl).
Proof.
  intros.
  unfold nt_keys.
  unfold pt_lookup in *.
  induction (ParseTable.elements tbl) eqn:Helts; simpl in *; subst.
  - unfold pt_lookup in H.
    unfold nt_keys.
Admitted.
 *)

(*
Program Fixpoint parse'' (tbl     : parse_table)
                         (sym_in  : sym_input)
                         (word    : list string)
                         (visited : list nonterminal)
                         {measure (parse_measure word tbl visited) (nat_lexprod)}
                         : sum parse_failure (sem_value * list string * list nonterminal) := 
  match sym_in with
  | inr sym =>
    (* morally, a call to parse *)
    match (sym, word) with
    | (T y, nil) => inl (Mismatch "error message" word)
    | (T y, token :: word') =>
      match beqString y token with
      | false => inl (Mismatch "error message" word)
      | true => inr (inr (Leaf y), word', nil)
      end
    | (NT x, _) =>
      if List.in_dec NT_as_DT.eq_dec x visited then
        inl (LeftRec (x :: visited))
      else
        match pt_lookup x (peek word) tbl with
        | None => inl (Mismatch "error message" word)
        | Some gamma =>
          match parse'' tbl (inl gamma) word (x :: visited) with
          | inl pf => inl pf
          | inr (inl sts, word', visited') => inr (inr (Node x sts), word', visited')
          | inr (inr _, _, _) => inl Error
          end
        end
    end
  | inl gamma =>
    match gamma with
    | nil => inr (inl nil, word, visited)
    | sym :: gamma' =>
      match parse'' tbl (inr sym) word visited with
      | inl pf => inl pf
      | inr (inr lSib, word', visited') =>
        match parse'' tbl (inl gamma') word' visited' with
        | inl pf => inl pf
        | inr (inl rSibs, word'', visited'') =>
          inr (inl (lSib :: rSibs), word'', visited'')
        | inr (inr _, _, _) => inl Error
        end
      | inr (inl _, _, _) => inl Error
      end
    end
  end.
Next Obligation.
  apply right_lex; simpl.
  apply NP.subset_cardinal_lt with (x := x); try ND.fsetdec.
  apply in_A_not_in_B_in_diff.
  - apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_tbl; eauto.
  - unfold not; intros.
    apply H.
    apply in_list_iff_in_fromNtList; auto.
Defined.
Next Obligation.
Admitted.
Next Obligation.
  simpl in *. inv Heq_anonymous.
Admitted.
Next Obligation.
  apply measure_wf.
  apply nat_lexprod_wf.
  constructor.
  intros.
Admitted.
 *)

Section TripleLT.

Variables (A B C : Type) (ltA : relation A) (ltB : relation B) (ltC : relation C).

Inductive triple_lex : A * B * C -> A * B * C -> Prop :=
| fst_lt : forall x x' y y' z z', ltA x x' -> triple_lex (x, y, z) (x', y', z')
| snd_lt : forall x y y' z z', ltB y y' -> triple_lex (x, y, z) (x, y', z')
| thd_lt : forall x y z z', ltC z z' -> triple_lex (x, y, z) (x, y, z').

Hint Constructors triple_lex.

Theorem triple_lex_trans :
  transitive _ ltA -> transitive _ ltB -> transitive _ ltC -> transitive _ triple_lex.
Proof.
  intros tA tB tC [[x1 y1] z1] [[x2 y2] z2] [[x3 y3] z3] H12 H23.
  inv H12; inv H23; eauto.
Qed.

Theorem triple_lex_wf :
  well_founded ltA -> well_founded ltB -> well_founded ltC -> well_founded triple_lex.
Proof.
  intros wfA wfB wfC [[x y] z].
  revert y z.
  induction (wfA x) as [x _ IHx].
  intros y.
  induction (wfB y) as [y _ IHy].
  intros z.
  induction (wfC z) as [z _ IHz].
  constructor.
  intros [[x' y'] z'] H.
  inv H; eauto.
Qed.

Definition lengthOrder (xs ys : list A) :=
  List.length xs < List.length ys.

Require Import Omega.

Require Import Wellfounded.Inverse_Image.

Theorem lengthOrder_wf : well_founded lengthOrder.
Proof.
  apply wf_inverse_image with (R := lt).
  apply lt_wf.
Defined.

Theorem lengthOrder_trans : transitive _ lengthOrder.
Proof.
  red; unfold lengthOrder; intros; omega.
Defined.
  
Definition cardOrder (s1 s2 : NtSet.t) :=
  NtSet.cardinal s1 < NtSet.cardinal s2.

Theorem cardOrder_trans : transitive _ cardOrder.
Proof.
  red; unfold cardOrder; intros; omega.
Defined.

Theorem cardOrder_wf : well_founded cardOrder.
Proof.
  apply wf_inverse_image with (R := lt).
  apply lt_wf.
Defined.

Definition bool_order (b1 b2 : bool) : Prop :=
  b1 = false /\ b2 = true.

Theorem bool_order_trans : transitive _ bool_order.
Proof.
  intros x y z Hxy Hyz.
  inv Hxy; inv Hyz; congruence.
Defined.
  
Theorem bool_order_wf : well_founded bool_order.
Proof.
  intros b2.
  constructor.
  intros b1 Hbo.
  inv Hbo.
  constructor.
  intros b1 Hbo.
  inv Hbo.
  congruence.
Defined.

End TripleLT.

Require Import Coq.Arith.Wf_nat.

Set Implicit Arguments.

Definition triple_lt : relation (nat * nat * bool) :=
  triple_lex nat nat bool lt lt bool_order.

Definition parse_measure (triple : list string * list nonterminal * bool) :=
  match triple with
  | (input, visited, b) => (List.length input, List.length visited, b)
  end.

Lemma input_decrease_lt :
  forall (tr' tr : list string * list nonterminal * bool)
         (token : string)
         (vis : list nonterminal)
         (b : bool),
    match tr' with
    | (input', vis', b') => 
      triple_lt (parse_measure tr') (parse_measure (token :: input', vis, b))
    end.
Proof.
  intros.
  destruct tr'.
  destruct p.
  apply fst_lt.
  simpl.
  omega.
Defined.

(*
Fixpoint parse (tbl : parse_table)
               (sym : symbol)
               (input : list string)
               (vis : list nonterminal)
               (b : bool)
               (a : Acc parse_triple_lt (parse_measure (input, vis, b)))
               {struct a}          
  : sum parse_failure (tree * {triple' | parse_triple_lt (parse_measure triple') (parse_measure (input, vis, b))}) :=
  match (sym, input) with
  | (T y, nil) => inl (Mismatch "error message" input)
  | (T y, token :: input') =>
    if beqString y token then
      inr (Leaf y, exist _
                         (input', nil, false)
                         (input_decrease_lt (input', nil, false)))
    else
      inl (Mismatch "error message" input)
  | (NT x, _) =>
    if List.in_dec NT_as_DT.eq_dec x visited then
      inl (LeftRec (x :: visited))
    else
      match pt_lookup x (peek input) tbl with
      | None => inl (Mismatch "error message" input)
      | Some gamma =>
        match parseForest tbl gamma (input, (x :: visited), true) _ with
        | inl pf => inl pf
        | inr (sts, _) =>
          inr (Node x sts, _)
        end
      end
  end
with parseForest (tbl : parse_table) 
                 (gamma : list symbol)
                 (triple : list string * list nonterminal * bool)
                 (a : Acc parse_triple_lt (parse_measure triple))
                 {struct a}
     : sum parse_failure (list tree * {triple' | triple' = triple \/ parse_triple_lt (parse_measure triple') (parse_measure triple)}) :=
       match triple with
       | (input, visited, b) =>
         match gamma with
         | nil => inr (nil, _)
         | sym :: gamma' =>
           match b with
           | false => inl Error
           | true =>
             match parse tbl sym (input, visited, false) _ with
             | inl pf => inl pf
             | inr (lSib, _) =>
               match parseForest tbl gamma' _ _ with
               | inl pf => inl pf
               | inr (rSibs, _) =>
                 inr (lSib :: rSibs, _)
               end
             end
           end
         end
       end.
 *)

Program Fixpoint div2 (n : nat) : { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
  match n with
  | S (S p) => S (div2 p)
  | _ => O
  end.
Obligation 1.
omega.
Defined.
Obligation 2.
destruct n.
- auto.
- destruct n.
  + auto.
  + specialize (H n).
    congruence.
Defined.

Inductive sym_arg : Set :=
| F_arg : symbol -> sym_arg
| G_arg : list symbol -> sym_arg.

Definition boolOf (sa : sym_arg) : bool :=
  match sa with
  | F_arg _ => false
  | G_arg _ => true
  end.

Definition nt_keys (tbl : parse_table) : list nonterminal :=
  List.map (fun pr => match pr with 
                      | ((x, _), _) => x
                      end)
           (ParseTable.elements tbl).

Definition meas (tbl : parse_table) (triple : list string * list nonterminal * sym_arg) : nat * nat * bool :=
  match triple with
  | (word, visited, sa) =>
    (List.length word,
     NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl)) (fromNtList visited)),
     boolOf sa)
  end.

Definition triple_le (tr1 tr2 : nat * nat * bool) : Prop :=
  triple_lt tr1 tr2 \/ tr1 = tr2.

Lemma not_in_list_iff_not_in_fromNtList:
  forall (x : NtSet.elt) (l : list NtSet.elt),
    ~ In x l <-> ~ NtSet.In x (fromNtList l).
Proof.
  split; unfold not; intros H1 H2.
  - apply H1.
    apply in_list_iff_in_fromNtList; auto.
  - apply H1.
    apply in_list_iff_in_fromNtList; auto.
Qed.

Lemma lt_trans : transitive nat lt.
Proof.
  red.
  apply Nat_as_DT.lt_trans.
Qed.

Lemma triple_lt_le_trans :
  forall (x y z : nat * nat * bool),
    triple_lt x y
    -> triple_le y z
    -> triple_lt x z.
Proof.
  intros x y z Hlt Hle.
  destruct Hle.
  - eapply triple_lex_trans; eauto.
    + apply lt_trans.
    + apply lt_trans.
    + apply bool_order_trans.
  - subst; auto.
Qed.

Lemma triple_le_lt_trans :
  forall (x y z : nat * nat * bool),
    triple_le x y
    -> triple_lt y z
    -> triple_lt x z.
Proof.
  intros x y z Hle Hlt.
  destruct Hle.
  - eapply triple_lex_trans; eauto.
    + apply lt_trans.
    + apply lt_trans.
    + apply bool_order_trans.
  - subst; auto.
Qed.

Lemma triple_lt_trans :
  forall (x y z : nat * nat * bool),
    triple_lt x y
    -> triple_lt y z
    -> triple_lt x z.
Proof.
  intros x y z Hxy Hyz.
  eapply triple_lex_trans; eauto.
  - apply lt_trans.
  - apply lt_trans.
  - apply bool_order_trans.
Qed.

Lemma pt_lookup_in_nt_keys :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> In x (nt_keys tbl).
Proof.
  intros.
  unfold nt_keys.
  apply pt_lookup_elements in H.
  induction (ParseTable.elements tbl).
  - inv H.
  - simpl in *.
    destruct H.
    + subst; auto.
    + right; auto.
Qed.
        
Program Fixpoint parse' (tbl     : parse_table)
                        (tri     : list string * list nonterminal * sym_arg)
                        {measure (meas tbl tri) (triple_lt)}
                        : sum parse_failure
                              (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl tri)})
                                   (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl tri)})) :=
  match tri with
  | (word, vis, sa) =>
    match sa with
    | F_arg sym =>
      (* morally, a call to parse *)
      match (sym, word) with
      | (T y, nil) => inl (Mismatch "error message" word)
      | (T y, token :: word') =>
        if beqString y token then
          inr (inr (Leaf y, (word', nil, sa)))
        else
          inl (Mismatch "error message" word)
      | (NT x, _) =>
        if List.in_dec NT_as_DT.eq_dec x vis then
          inl (LeftRec (x :: vis))
        else
          match pt_lookup x (peek word) tbl with
          | None => inl (Mismatch "error message" word)
          | Some gamma =>
            match parse' tbl (word, x :: vis, G_arg gamma) with
            | inl pf => inl pf
            | inr (inr (_, _)) => inl Error
            | inr (inl (sts, exist _ tri' _)) => inr (inr (Node x sts, exist _ tri' _))
            end
          end
      end
    | G_arg gamma =>
      (* a call to parseForest *)
      match gamma with
      | nil => inr (inl (nil, (word, vis, sa)))
      | sym :: gamma' =>
        match parse' tbl (word, vis, F_arg sym) with
        | inl pf => inl pf
        | inr (inl (_, _)) => inl Error
        | inr (inr (lSib, exist _ tri' _)) =>
          match parse' tbl tri' with
          | inl pf => inl pf
          | inr (inr (_, _)) => inl Error
          | inr (inl (rSibs, exist _ tri'' _)) =>
            inr (inl (lSib :: rSibs, exist _ tri'' _))
          end
        end
      end
    end
  end.
Obligation 1.
apply fst_lt; auto.
Defined.
Obligation 2.
simpl.
apply snd_lt.
apply NP.subset_cardinal_lt with (x := x).
- ND.fsetdec. 
- apply in_A_not_in_B_in_diff.
  + apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_nt_keys; eauto.
  + apply not_in_list_iff_not_in_fromNtList; auto.
- ND.fsetdec.
Defined.
Obligation 3.
destruct Heq_tri.
eapply triple_le_lt_trans; eauto.
apply snd_lt.
apply NP.subset_cardinal_lt with (x := x).
- ND.fsetdec. 
- apply in_A_not_in_B_in_diff.
  + apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_nt_keys; eauto.
  + apply not_in_list_iff_not_in_fromNtList; auto.
- ND.fsetdec.
Defined.
Obligation 4.
red; auto.
Defined.
Obligation 5.
apply thd_lt; red; auto.
Defined.
Obligation 6.
destruct Heq_tri.
simpl.
eapply triple_lt_trans; eauto.
apply thd_lt; red; auto.
Defined.
Obligation 7.
(* there might be a shorter proof for this one *)
destruct Heq_tri.
left.
eapply triple_le_lt_trans; eauto.
eapply triple_lt_trans; eauto.
apply thd_lt; red; auto.
Defined.
Obligation 8.
apply measure_wf.
apply triple_lex_wf.
- apply lt_wf.
- apply lt_wf.
- apply bool_order_wf.
Defined.

(* Plan :

   - replace obligations with proof terms (* done! *)
   - add Acc arg
   - see if Function allows you to prove termination as separate obligations
   - switch to two mutually recursive functions *)

Lemma tail_lt_word :
  forall tbl tri word token word' vis vis' sa sa',
    tri = (word, vis, sa)
    -> word = token :: word'
    -> triple_lt (meas tbl (word', vis', sa')) (meas tbl tri).
Proof.
  intros.
  subst.
  apply fst_lt; auto.
Qed.

Lemma vis_lt_add :
  forall tbl (tri tri' : list string * list nonterminal * sym_arg) word vis sa sa' x gamma,
    tri = (word, vis, sa)
    -> ~ In x vis
    -> pt_lookup x (peek word) tbl = Some gamma
    -> triple_le (meas tbl tri') (meas tbl (word, x :: vis, sa'))
    -> triple_lt (meas tbl tri') (meas tbl tri).
Proof.
  intros; subst.
  eapply triple_le_lt_trans; eauto.
  apply snd_lt; simpl.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec. 
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Qed.

Lemma triple_le_refl :
  forall tbl tri word vis sa,
    tri = (word, vis, sa)
    -> triple_le (meas tbl (word, vis, sa)) (meas tbl tri).
Proof.
  intros; subst.
  right; auto.
Qed.

Lemma pf_lt_args :
  forall tbl tri tri' tri'' word vis sa gamma sym gamma',
    tri = (word, vis, sa)
    -> sa = G_arg gamma
    -> gamma = sym :: gamma'
    -> triple_lt (meas tbl tri') (meas tbl (word, vis, F_arg sym))
    -> triple_le (meas tbl tri'') (meas tbl tri')
    -> triple_le (meas tbl tri'') (meas tbl tri).
Proof.
  intros; subst.
  left.
  eapply triple_le_lt_trans; eauto.
  eapply triple_lt_trans; eauto.
  apply thd_lt; red; auto.
Qed.

(* to do : some of the match annotations might actually be unnecessary *)
Fixpoint parse' (tbl     : parse_table)
         (tri     : list string * list nonterminal * sym_arg)
  : sum parse_failure
        (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl tri)})
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl tri)})).
  refine (match tri as tri' return tri = tri' -> _ with
          | (word, vis, sa) =>
            fun Htri => match sa as sa' return sa = sa' -> _ with
                        | F_arg sym =>
                          (* morally, a call to parse *)
                          fun _ => match sym with
                                   | T y  => match word as w return word = w -> _ with
                                             | [] => fun _ => inl (Mismatch "error message" word)
                                             | token :: word' =>
                                               if beqString y token then
                                                 fun Hword =>
                                                   inr (inr (Leaf y, exist _ (word', nil, sa) (tail_lt_word tbl _ _ Htri Hword)))
                                               else
                                                 fun _ => inl (Mismatch "error message" word)
                                             end eq_refl
                                   | NT x =>
                                     match List.in_dec NT_as_DT.eq_dec x vis with
                                     | left _ => inl (LeftRec (x :: vis))
                                     | right Hnin => 
                                       match pt_lookup x (peek word) tbl as H return  pt_lookup x (peek word) tbl = H -> _ with
                                       | None => fun _ => inl (Mismatch "error message" word)
                                       | Some gamma =>
                                         fun Hlk => match parse' tbl (word, x :: vis, G_arg gamma) with
                                                    | inl pf => inl pf
                                                    | inr (inr (_, _)) => inl Error
                                                    | inr (inl (sts, exist _ tri' Htri')) =>
                                                      inr (inr (Node x sts, exist _ tri' (vis_lt_add tri' Htri Hnin Hlk Htri')))
                                                    end
                                       end eq_refl
                                     end
                                   end
                        | G_arg gamma =>
                          (* a call to parseForest *)
                          fun Hsa => match gamma as g return gamma = g -> _ with
                                     | nil =>
                                       fun _ => inr (inl (nil, exist _ (word, vis, sa) (triple_le_refl tbl Htri)))
                                     | sym :: gamma' =>
                                       fun Hgamma => match parse' tbl (word, vis, F_arg sym) with
                                                     | inl pf => inl pf
                                                     | inr (inl (_, _)) => inl Error
                                                     | inr (inr (lSib, exist _ tri' Htri')) =>
                                                       match parse' tbl tri' with
                                                       | inl pf => inl pf
                                                       | inr (inr (_, _)) => inl Error
                                                       | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                         inr (inl (lSib :: rSibs, exist _ tri'' (pf_lt_args _ _ Htri Hsa Hgamma Htri' Htri'')))
                                                       end
                                                     end
                                     end eq_refl
                        end eq_refl
          end eq_refl).
Defined.

Definition isLeft (A B : Type) (e : sum A B) : bool :=
  match e with
  | inl _ => true
  | inr _ => false
  end.

Definition isRight (A B : Type) (e : sum A B) : bool :=
  negb (isLeft e).

Definition triple_lt_ind :=
  triple_lex_ind nat nat bool lt lt bool_order.

(*
Lemma parse'_eq_body :
  forall (tbl : parse_table)
         (tri : list string * list nonterminal * sym_arg),
  exists pf1 pf2 pf3 pf4,
      parse' tbl tri =
      match tri with
      | (word, vis, sa) =>
        match sa with
        | F_arg sym =>
          (* morally, a call to parse *)
          match (sym, word) with
          | (T y, nil) => inl (Mismatch "error message" word)
          | (T y, token :: word') =>
            if beqString y token then
              inr (inr (Leaf y, exist _ (word', nil, sa) (pf1 word' sa)))
            else
              inl (Mismatch "error message" word)
          | (NT x, _) =>
            if List.in_dec NT_as_DT.eq_dec x vis then
              inl (LeftRec (x :: vis))
            else
              match pt_lookup x (peek word) tbl with
              | None => inl (Mismatch "error message" word)
              | Some gamma =>
                match parse' tbl (word, x :: vis, G_arg gamma) with
                | inl pf => inl pf
                | inr (inr (_, _)) => inl Error
                | inr (inl (sts, exist _ tri' _)) => inr (inr (Node x sts, exist _ tri' (pf2 tri')))
                end
              end
          end
        | G_arg gamma =>
          (* a call to parseForest *)
          match gamma with
          | nil => inr (inl (nil, exist _ (word, vis, sa) (pf3 word vis sa)))
          | sym :: gamma' =>
            match parse' tbl (word, vis, F_arg sym) with
            | inl pf => inl pf
            | inr (inl (_, _)) => inl Error
            | inr (inr (lSib, exist _ tri' _)) =>
              match parse' tbl tri' with
              | inl pf => inl pf
              | inr (inr (_, _)) => inl Error
              | inr (inl (rSibs, exist _ tri'' _)) =>
                inr (inl (lSib :: rSibs, exist _ tri'' (pf4 tri'')))
              end
            end
          end
        end
      end.
Proof.
  intros.
  do 4 eexists.
  unfold parse'.
  unfold parse'_func.
  rewrite Wf.fix_sub_eq.
  - destruct tri as [[word vis] sa].
    cbv zeta.
    lazy beta.
    cbv zeta. *)

Lemma sym_ret_inr :
  forall (tbl : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         e,
    parse' tbl (word, vis, sa) = inr e
    -> forall (sym : symbol),
      sa = F_arg sym
      -> isRight e = true.
Proof.
  intros.
  induction word as [| tok word'].
  - unfold parse' in H.
    unfold parse'_func in H. subst.
    destruct e.
    + destruct p.
      inv H.
      
    simpl in *.
    destruct sym.
    + unfold parse' in H.
      unfold parse'_func in H.
      simpl in *.
  

