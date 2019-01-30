Require Import FMaps List MSets Omega String Program.Wf Arith.Wf_nat.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Utils.
Require Import Lib.Tactics.
Require Import LL1.Derivation.
Require Import LL1.ParseTable. 
Require Import LL1.ParseTableGen. (* for fromNtList *)
Import ListNotations.
Open Scope string_scope.

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
Defined.
      
Lemma pt_lookup_elements :
  forall x la tbl gamma,
    pt_lookup x la tbl = Some gamma
    -> In ((x, la), gamma) (ParseTable.elements tbl).
Proof.
  intros.
  unfold pt_lookup in *.
  rewrite ParseTableFacts.elements_o in H.
  apply pt_lookup_elements'; auto.
Defined.

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
  Defined.

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
  Defined.

End TripleLT.

Inductive sym_arg : Set :=
| F_arg : symbol -> sym_arg
| G_arg : list symbol -> sym_arg.

Definition nt_keys (tbl : parse_table) : list nonterminal :=
  List.map (fun pr => match pr with 
                      | ((x, _), _) => x
                      end)
           (ParseTable.elements tbl).

Lemma not_in_list_iff_not_in_fromNtList:
  forall (x : NtSet.elt) (l : list NtSet.elt),
    ~ In x l <-> ~ NtSet.In x (fromNtList l).
Proof.
  split; unfold not; intros H1 H2.
  - apply H1.
    apply in_list_iff_in_fromNtList; auto.
  - apply H1.
    apply in_list_iff_in_fromNtList; auto.
Defined.

Lemma lt_trans : transitive nat lt.
Proof.
  red.
  apply Nat_as_DT.lt_trans.
Defined.

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
Defined.
        
Definition ptlk_dec x la tbl : sum (pt_lookup x la tbl = None) {gamma | pt_lookup x la tbl = Some gamma}.
  destruct (pt_lookup x la tbl) eqn:Hlk.
  - right.
    econstructor; eauto.
  - left.
    auto.
Defined.

Definition X := 0.
Definition Y := 1.
Definition Z := 2.

Definition yy_grammar :=
  {|
     start := X
   ; productions := [(X, [NT Y; NT Y; T "a"]);
                     (Y, [])]
  |}.

Definition a_generator :=
  {|
     start := X
   ; productions := [(X, [T "a"; NT X]);
                     (X, [])]
  |}.

Definition lr_table :=
  ParseTable.add (X, LA "a") [NT Y; NT Z]
                 (ParseTable.add (Y, LA "a") []
                                 (ParseTable.add (Z, LA "a") [NT X]
                                                 (ParseTable.empty (list symbol)))).

Inductive sa_order : sym_arg -> sym_arg -> Prop := 
| f_lt_g : forall sym gamma,
    sa_order (F_arg sym) (G_arg gamma)
| g'_lt_g : forall gamma' gamma,
    List.length gamma' < List.length gamma
    -> sa_order (G_arg gamma') (G_arg gamma).

Definition meas tbl (word : list string) (vis : list nonterminal) (sa : sym_arg) :=
  (List.length word,
   NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))                                     (fromNtList vis)),
   sa).

Definition triple_lt : relation (nat * nat * sym_arg) :=
  triple_lex nat nat sym_arg lt lt sa_order.

Lemma sa_order_wf'' :
  forall sym, Acc sa_order (F_arg sym).
Proof.
  intros.
  constructor; intros a H.
  inv H.
Defined.

Lemma sa_order_wf' :
  forall n gamma,
    List.length gamma < n
    -> Acc sa_order (G_arg gamma).
Proof.
  induction n; intros gamma H; simpl in *.
  - inv H.
  - constructor; intros a Ha.
    inv Ha; simpl in *.
    + apply sa_order_wf''.
    + apply IHn; omega.
Defined.

Theorem sa_order_wf : well_founded sa_order.
Proof.
  red; intros a; destruct a.
  - apply sa_order_wf''.
  - eapply sa_order_wf'; eauto.
Defined.

Theorem triple_lt_wf : well_founded triple_lt.
  apply triple_lex_wf; try apply lt_wf.
  apply sa_order_wf.
Defined.

Lemma hole1 :
  forall tbl input vis sa sa' x gamma,
    Acc triple_lt (meas tbl input vis sa)
    -> pt_lookup x (peek input) tbl = Some gamma
    -> ~ In x vis
    -> Acc triple_lt (meas tbl input (x :: vis) sa').
Proof.
  intros.
  eapply Acc_inv; eauto.
  unfold meas.
  apply snd_lt; simpl.
  apply NP.subset_cardinal_lt with (x := x); try ND.fsetdec.
  apply in_A_not_in_B_in_diff.
  - apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_nt_keys; eauto.
  - apply not_in_list_iff_not_in_fromNtList; auto.
Defined.

Lemma hole2 :
  forall tbl input vis gamma sym,
    Acc triple_lt (meas tbl input vis (G_arg gamma))
    -> Acc triple_lt (meas tbl input vis (F_arg sym)).
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply thd_lt; constructor.
Defined.

Lemma hole3 :
  forall tbl input input' vis vis' sa sa',
    Acc triple_lt (meas tbl input vis sa)
    -> List.length input' < List.length input
    -> Acc triple_lt (meas tbl input' vis' sa').
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply fst_lt; auto.
Defined.

Lemma hole4 :
  forall tbl input vis gamma sym gamma',
    Acc triple_lt (meas tbl input vis (G_arg gamma))
    -> gamma = sym :: gamma'
    -> Acc triple_lt (meas tbl input vis (G_arg gamma')).
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply thd_lt; subst.
  constructor; auto.
Defined.

Fixpoint p (tbl : parse_table)
         (sym : symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc triple_lt (meas tbl input vis (F_arg sym)))
         {struct a}
         : (option tree * list string) :=
  match (sym, input) with
  | (T _, nil) => (None, input)
  | (T y, token :: input') =>
    if beqString y token then
      (Some (Leaf y), input')
    else
      (None, input)
  | (NT x, _) =>
    match ptlk_dec x (peek input) tbl with
    | inl _ => (None, input)
    | inr (exist _ gamma Hlk) =>
      match List.in_dec NT_as_DT.eq_dec x vis with
      | left _ => (None, input)
      | right Hnin => 
        match pf tbl gamma input (x :: vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
        | (None, _) => (None, input)
        | (Some sts, input') =>
          (Some (Node x sts), input')
        end
      end
    end
  end
with pf (tbl : parse_table)
        (gamma : list symbol)
        (input : list string)
        (vis : list nonterminal)
        (a : Acc triple_lt (meas tbl input vis (G_arg gamma)))
        {struct a}
        : (option (list tree) * list string) :=
       match gamma as g return gamma = g -> _  with
       | nil => fun _ => (Some nil, input)
       | sym :: gamma' => fun Hg => 
                            match p tbl sym input vis (hole2 _ _ _ _ _ a) with
                            | (None, _) => (None, input)
                            | (Some lSib, input') =>
                              match Compare_dec.lt_dec (List.length input') (List.length input) with
                              | left Hlt =>
                                match pf tbl gamma' input' [] (hole3 _ _ _ _ _ _ _ a Hlt) with
                                | (None, _) => (None, input)
                                | (Some rSibs, input'') =>
                                  (Some (lSib :: rSibs), input'')
                                end
                              | right Hnlt =>
                                match pf tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                                | (None, _) => (None, input)
                                | (Some rSibs, input'') =>
                                  (Some (lSib :: rSibs), input'')
                                end
                              end
                            end
       end eq_refl.

Extraction p.

Definition parse_wrapper tbl sym input vis :=
  p tbl sym input vis (triple_lt_wf (meas tbl input vis (F_arg sym))).

(*
Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (parse_wrapper tbl (NT X) ["a"] [])
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (parse_wrapper tbl (NT X) ["a"; "a"; "a"] [])
                end.

Eval compute in parse_wrapper lr_table (NT X) ["a"] [].
*)

Ltac step_h := match goal with
               | H : context[match ?x with | _ => _ end] |- _ => destruct x
              end.

Ltac step_h_eq s := let Heq := fresh s in
                    match goal with
                    | H : context[match ?x with | _ => _ end] |- _ =>
                      destruct x eqn:Heq
                    end.

Ltac step_g := match goal with
               | |- context[match ?x with | _ => _ end] => destruct x
               end.

Ltac step := simpl in *; (first [step_h | step_g]); auto.
Ltac step_eq s := simpl in *; (first [step_h_eq s | step_g]); auto.
Ltac cr := repeat step.
Ltac cr_eq s := repeat (step_eq s).
Ltac tc := try congruence.

Lemma p_eq_body :
  forall (tbl : parse_table)
         (sym : symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
    p tbl sym input vis a =
    match (sym, input) with
    | (T _, nil) => (None, input)
    | (T y, token :: input') =>
      if beqString y token then
        (Some (Leaf y), input')
      else
        (None, input)
    | (NT x, _) =>
      match ptlk_dec x (peek input) tbl with
      | inl _ => (None, input)
      | inr (exist _ gamma Hlk) =>
        match List.in_dec NT_as_DT.eq_dec x vis with
        | left _ => (None, input)
        | right Hnin => 
          match pf tbl gamma input (x :: vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
          | (None, _) => (None, input)
          | (Some sts, input') =>
            (Some (Node x sts), input')
          end
        end
      end
    end.
Proof.
  intros; destruct a; simpl; cr.
Qed.

Lemma pf_eq_body :
  forall (tbl : parse_table)
         (gamma : list symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc triple_lt (meas tbl input vis (G_arg gamma))),
    pf tbl gamma input vis a =
    match gamma as g return gamma = g -> _  with
    | nil => fun _ => (Some nil, input)
    | sym :: gamma' => fun Hg => 
                         match p tbl sym input vis (hole2 _ _ _ _ _ a) with
                         | (None, _) => (None, input)
                         | (Some lSib, input') =>
                           match Compare_dec.lt_dec (List.length input') (List.length input) with
                           | left Hlt =>
                             match pf tbl gamma' input' [] (hole3 _ _ _ _ _ _ _ a Hlt) with
                             | (None, _) => (None, input)
                             | (Some rSibs, input'') =>
                               (Some (lSib :: rSibs), input'')
                             end
                           | right Hnlt =>
                             match pf tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                             | (None, _) => (None, input)
                             | (Some rSibs, input'') =>
                               (Some (lSib :: rSibs), input'')
                             end
                           end
                         end
    end eq_refl.
Proof.
  intros; destruct a; cr.
Qed.

Lemma p_t_ret_leaf :
  forall tbl
         input rem
         vis
         y
         (a : Acc triple_lt (meas tbl input vis (F_arg (T y))))
         tr,
    p tbl (T y) input vis a = (Some tr, rem)
    -> isLeaf tr = true.
Proof.
  intros; destruct a; cr; tc.
  inv H; auto.
Qed.

Lemma p_nt_ret_node :
  forall tbl
         input rem
         vis
         x
         (a : Acc triple_lt (meas tbl input vis (F_arg (NT x))))
         tr,
    p tbl (NT x) input vis a = (Some tr, rem)
    -> isNode tr = true.
Proof.
  intros; destruct a; cr; tc.
  inv H; auto.
Qed.

Open Scope list_scope.

Lemma l_ident_eq_nil :
  forall A (xs ys : list A), xs ++ ys = ys -> xs = [].
Proof.
  intros.
  rewrite <- app_nil_l in H.
  apply app_inv_tail in H; auto.
Qed.

Lemma input_length_invariant :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              (vis       : list nonterminal)
              (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
      p tbl sym input vis a = (Some tr, rem)
      -> List.length rem < List.length input
         \/ rem = input.
Proof.
  intros g tbl Htbl tr.
  induction tr as [ s
                  | s f IHpf
                  |
                  | tr IHp f IHpf ]
                    using tree_nested_ind with
      
      (Q := fun f =>
              forall (gamma : list symbol)
                     (input rem : list string)
                     (vis : list nonterminal)
                     (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                pf tbl gamma input vis a = (Some f, rem)
                -> List.length rem < List.length input
                   \/ rem = input); intros; destruct a.

  - destruct sym as [y | x].
    + cr; tc.
      inv H; auto.
    + apply p_nt_ret_node in H; inv H.

  - destruct sym as [y | x].
    + apply p_t_ret_leaf in H; inv H.
    + step; tc.
      step.
      step; tc.
      step_eq Hpf.
      step; tc.
      inv H.
      apply IHpf in Hpf; auto.

  - cr; tc.
    inv H; auto.

  - step; tc.
    step_eq Hp.
    step; tc.
    step.
    + step_eq Hpf.
      step; tc.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf.
      * left; omega.
      * subst; auto.
    + step_eq Hpf.
      step; tc.
      inv H.
      apply IHpf in Hpf; clear IHpf.
      auto.
Qed.
          
Lemma p_sound' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              (vis       : list nonterminal)
              (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
      p tbl sym input vis a = (Some tr, rem)
      -> exists word,
        word ++ rem = input
        /\ (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr.
  induction tr as [ s
                  | s f IHpf
                  |
                  | tr IHp f IHpf ]
                    using tree_nested_ind with

      (Q := fun f =>
              forall (gamma : list symbol)
                     (input rem : list string)
                     (vis : list nonterminal)
                     (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                pf tbl gamma input vis a = (Some f, rem)
                -> exists word,
                  word ++ rem = input
                  /\ gamma_derives_prefix gamma word f rem); intros; destruct a.

  - destruct sym as [y | x].
    + rewrite p_eq_body in H.
      step; tc.
      step_eq Hbeq; tc.
      inv H.
      eexists; split.
      * rewrite cons_app_singleton; auto.
      * rewrite beqSym_eq in Hbeq; subst.
        constructor; auto.
    + apply p_nt_ret_node in H; inv H.

  - destruct sym as [y | x].
    + apply p_t_ret_leaf in H; inv H.
    + simpl in H.
      destruct (ptlk_dec x (peek input) tbl) as [| e]; tc.
      destruct e as [gamma Hlk].
      step; tc.
      step_eq Hpf.
      step; tc.
      inv H.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf as [word [Happ Hg]]; subst.
      eexists; split; eauto.
      apply Htbl in Hlk; destruct Hlk.
      econstructor; eauto.

  - rewrite pf_eq_body in H.
    cr; tc.
    inv H.
    exists nil; split; auto.
    constructor.

  - rewrite pf_eq_body in H.
    step; tc.
    step_eq Hp.
    step; tc.
    step.
    + step_eq Hpf.
      step; tc.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp  as [wpre [Happ Hs]]; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists (wpre ++ wsuf); split.
      * rewrite app_assoc; auto.
      * constructor; auto.
    + pose proof Hp as Hp'.
      eapply input_length_invariant in Hp'; eauto.
      destruct Hp'; try contradiction.
      subst.
      step_eq Hpf.
      step; tc.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp as [wpre [Happ Hs]].
      apply l_ident_eq_nil in Happ; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists ([] ++ wsuf); split; auto.
      constructor; auto.
Qed.

Lemma p_sound :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (word rem  : list terminal)
              (vis       : list nonterminal)
              (a : Acc triple_lt (meas tbl (word ++ rem) vis (F_arg sym))),
      p tbl sym (word ++ rem) vis a = (Some tr, rem)
      -> (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr sym word rem vis a Hp.
  pose proof Hp as Hp'.
  eapply p_sound' in Hp; eauto.
  destruct Hp as [word' [Happ Hder]].
  apply app_inv_tail in Happ.
  subst; auto.
Qed.

Inductive parse_failure : Set :=
| Reject   : string -> list string -> parse_failure
| LeftRec  : nonterminal -> list nonterminal -> list string -> parse_failure.

Fixpoint p2 (tbl : parse_table)
            (sym : symbol)
            (input : list string)
            (vis : list nonterminal)
            (a : Acc triple_lt (meas tbl input vis (F_arg sym)))
            {struct a}
            : sum parse_failure (tree * list string) :=
  match (sym, input) with
  | (T _, nil) => inl (Reject "input exhausted" input)
  | (T y, token :: input') =>
    if string_dec y token then
      inr (Leaf y, input')
    else
      inl (Reject "token mismatch" input)
  | (NT x, _) =>
    match ptlk_dec x (peek input) tbl with
    | inl _ => inl (Reject "lookup failure" input)
    | inr (exist _ gamma Hlk) =>
      match List.in_dec NT_as_DT.eq_dec x vis with
      | left _ => inl (LeftRec x vis input)
      | right Hnin => 
        match pf2 tbl gamma input (x :: vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
        | inl pfail => inl pfail
        | inr (sts, input') =>
          inr (Node x sts, input')
        end
      end
    end
  end
with pf2 (tbl : parse_table)
         (gamma : list symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc triple_lt (meas tbl input vis (G_arg gamma)))
         {struct a}
         : sum parse_failure (list tree * list string) :=
       match gamma as g return gamma = g -> _  with
       | nil => fun _ => inr (nil, input)
       | sym :: gamma' => fun Hg => 
                            match p2 tbl sym input vis (hole2 _ _ _ _ _ a) with
                            | inl pfail => inl pfail
                            | inr (lSib, input') =>
                              match Compare_dec.lt_dec (List.length input') (List.length input) with
                              | left Hlt =>
                                match pf2 tbl gamma' input' [] (hole3 _ _ _ _ _ _ _ a Hlt) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              | right Hnlt =>
                                match pf2 tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              end
                            end
       end eq_refl.

Lemma p2_eq_body :
  forall tbl sym input vis a,
    p2 tbl sym input vis a = 
  match (sym, input) with
  | (T _, nil) => inl (Reject "input exhausted" input)
  | (T y, token :: input') =>
    if string_dec y token then
      inr (Leaf y, input')
    else
      inl (Reject "token mismatch" input)
  | (NT x, _) =>
    match ptlk_dec x (peek input) tbl with
    | inl _ => inl (Reject "lookup failure" input)
    | inr (exist _ gamma Hlk) =>
      match List.in_dec NT_as_DT.eq_dec x vis with
      | left _ => inl (LeftRec x vis input)
      | right Hnin => 
        match pf2 tbl gamma input (x :: vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
        | inl pfail => inl pfail
        | inr (sts, input') =>
          inr (Node x sts, input')
        end
      end
    end
  end.
Proof.
  intros; simpl; destruct a; cr.
Qed.

(*
with pf2 (tbl : parse_table)
         (gamma : list symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc triple_lt (meas tbl input vis (G_arg gamma)))
         {struct a}
         : sum parse_failure (list tree * list string) :=
       match gamma as g return gamma = g -> _  with
       | nil => fun _ => inr (nil, input)
       | sym :: gamma' => fun Hg => 
                            match p2 tbl sym input vis (hole2 _ _ _ _ _ a) with
                            | inl pfail => inl pfail
                            | inr (lSib, input') =>
                              match Compare_dec.lt_dec (List.length input') (List.length input) with
                              | left Hlt =>
                                match pf2 tbl gamma' input' [] (hole3 _ _ _ _ _ _ _ a Hlt) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              | right Hnlt =>
                                match pf2 tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              end
                            end
       end eq_refl.

Lemma p2_sound' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              (vis       : list nonterminal)
              (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
      p2 tbl sym input vis a = inr (tr, rem)
      -> exists word,
        word ++ rem = input
        /\ (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr.
  induction tr as [ s
                  | s f IHpf
                  |
                  | tr IHp f IHpf ]
                    using tree_nested_ind with

      (Q := fun f =>
              forall (gamma : list symbol)
                     (input rem : list string)
                     (vis : list nonterminal)
                     (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                pf2 tbl gamma input vis a = inr (f, rem)
                -> exists word,
                  word ++ rem = input
                  /\ gamma_derives_prefix gamma word f rem); intros; destruct a.

  - destruct sym as [y | x].
    + rewrite p2_eq_body in H.
      step; tc.
      step_eq Hbeq; tc.
      inv H.
      eexists; split.
      * rewrite cons_app_singleton; auto.
      * rewrite beqSym_eq in Hbeq; subst.
        constructor; auto.
    + apply p_nt_ret_node in H; inv H.

  - destruct sym as [y | x].
    + apply p_t_ret_leaf in H; inv H.
    + simpl in H.
      destruct (ptlk_dec x (peek input) tbl) as [| e]; tc.
      destruct e as [gamma Hlk].
      step; tc.
      step_eq Hpf.
      step; tc.
      inv H.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf as [word [Happ Hg]]; subst.
      eexists; split; eauto.
      apply Htbl in Hlk; destruct Hlk.
      econstructor; eauto.

  - rewrite pf_eq_body in H.
    cr; tc.
    inv H.
    exists nil; split; auto.
    constructor.

  - rewrite pf_eq_body in H.
    step; tc.
    step_eq Hp.
    step; tc.
    step.
    + step_eq Hpf.
      step; tc.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp  as [wpre [Happ Hs]]; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists (wpre ++ wsuf); split.
      * rewrite app_assoc; auto.
      * constructor; auto.
    + pose proof Hp as Hp'.
      eapply input_length_invariant in Hp'; eauto.
      destruct Hp'; try contradiction.
      subst.
      step_eq Hpf.
      step; tc.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp as [wpre [Happ Hs]].
      apply l_ident_eq_nil in Happ; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists ([] ++ wsuf); split; auto.
      constructor; auto.
Qed.


Inductive nullable_path g (la : lookahead) :
  nonterminal -> nonterminal -> Prop :=
| DirectPath : forall x z gamma pre suf,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT z :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path g la x z
| IndirectPath : forall x y z gamma pre suf,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT y :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path g la y z
    -> nullable_path g la x z.

Inductive nullable_path_exp g (la : lookahead) :
  nonterminal -> nonterminal -> list nonterminal -> Prop :=
| DirectPath' : forall x z gamma pre suf,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT z :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path_exp g la x z [x ; z]
| IndirectPath' : forall x y z gamma pre suf tl,
    In (x, gamma) (productions g)
    -> gamma = pre ++ NT y :: suf
    -> nullable_gamma g pre
    -> lookahead_for la x gamma g
    -> nullable_path_exp g la y z tl
    -> nullable_path_exp g la x z (x :: tl).

Definition left_recursive g x la :=
  nullable_path g la x x.

Lemma nt_first_exists' :
  forall g sym x la,
    first_sym g la sym
    -> sym = NT x
    -> exists pre sym' suf,
        In (x, pre ++ sym' :: suf) (productions g)
        /\ nullable_gamma g pre
        /\ first_sym g la sym'
        /\ NT x <> sym'.
Proof.
  intros g sym x la Hf.
  induction Hf; intros He.
  - inv He.
  - inv He.
    destruct s as [y | x'].
    + clear IHHf.
      repeat eexists; eauto.
      congruence.
    + destruct (NT_as_DT.eq_dec x x'); subst.
      * apply IHHf; auto.
      * repeat eexists; eauto.
        congruence.
Qed.

Lemma nt_first_exists :
  forall g x la,
    first_sym g la (NT x)
    -> exists pre sym' suf,
      In (x, pre ++ sym' :: suf) (productions g)
      /\ nullable_gamma g pre
      /\ first_sym g la sym'
      /\ NT x <> sym'.
Proof.
  intros.
  eapply nt_first_exists'; eauto.
Qed.

Inductive fg' (g : grammar) (la : lookahead) :
  list symbol -> Prop :=
| fg_hd : forall h t,
    first_sym g la h
    -> fg' g la (h :: t)
| fg_tl : forall h t,
    nullable_sym g h
    -> fg' g la t
    -> fg' g la (h :: t).

Lemma fg_fg' :
  forall g la gamma,
    first_gamma g la gamma <-> fg' g la gamma.
Proof.
  intros g la gamma; split; intros H.
  - inv H.
    revert H0.
    revert H1.
    revert s gsuf.
    induction gpre; intros; simpl in *.
    + constructor; auto.
    + inv H0.
      apply fg_tl; auto.
  - induction H.
    + rewrite <- app_nil_l.
      constructor; auto.
    + inv IHfg'.
      apply FirstGamma with (gpre := h :: gpre)
                            (s := s)
                            (gsuf := gsuf); auto.
Qed.

Lemma medial :
  forall A pre pre' (sym sym' : A) suf suf',
    pre ++ sym :: suf = pre' ++ sym' :: suf'
    -> In sym pre' \/ In sym' pre \/ sym = sym'.
Proof.
  induction pre; intros; simpl in *.
  - destruct pre' eqn:Hp; simpl in *.
    + inv H; auto.
    + inv H; auto.
  - destruct pre' eqn:Hp; subst; simpl in *.
    + inv H; auto.
    + inv H.
      apply IHpre in H2.
      destruct H2; auto.
      destruct H; auto.
Qed.

Lemma nullable_sym_in :
  forall g sym gamma,
    nullable_gamma g gamma
    -> In sym gamma
    -> nullable_sym g sym.
Proof.
  intros.
  induction gamma.
  - inv H0.
  - inv H.
    inv H0; auto.
Qed.

Lemma first_gamma_split :
  forall g la xs ys,
    first_gamma g la ys
    -> nullable_gamma g xs
    -> first_gamma g la (xs ++ ys).
Proof.
  induction xs; intros; simpl in *; auto.
  inv H0.
  apply fg_fg'.
  apply fg_tl; auto.
  apply fg_fg'.
  auto.
Qed.

Lemma follow_pre :
  forall g x la sym suf pre,
    In (x, pre ++ suf) (productions g)
    -> In sym pre
    -> nullable_gamma g pre
    -> first_gamma g la suf
    -> follow_sym g la sym.
Proof.
  intros.
  apply in_split in H0.
  destruct H0 as [l1 [l2 Heq]].
  subst.
  destruct sym.
  - exfalso.
    eapply Lemmas.gamma_with_terminal_not_nullable; eauto. 
  - replace ((l1 ++ NT n :: l2) ++ suf) with (l1 ++ NT n :: (l2 ++ suf)) in H.
    + eapply FollowRight; eauto.
      apply Lemmas.nullable_split in H1.
      inv H1.
      apply first_gamma_split; auto.
    + rewrite cons_app_singleton.
      rewrite app_assoc.
      rewrite app_assoc.
      replace (((l1 ++ [NT n]) ++ l2)) with (l1 ++ NT n :: l2).
      * auto.
      * rewrite <- app_assoc; simpl; auto.
Qed.

Lemma no_direct_left_recursion_in_LL1_first' :
  forall g t la sym,
    parse_table_for t g
    -> first_sym g la sym
    -> forall x pre suf,
        NT x = sym
        -> nullable_gamma g pre
        -> In (x, pre ++ sym :: suf) (productions g)
        -> False.
Proof.
  intros g t la sym Ht Hf; induction Hf.
  - intros x pre suf He Hn Hi; inv He.
  - intros x' pre suf He Hn Hi; inv He.
    assert (Heq : gpre ++ s :: gsuf = pre ++ NT x :: suf).
    { assert (Hl : lookahead_for la x (gpre ++ s :: gsuf) g).
      { left; auto. }
      assert (Hl' : lookahead_for la x (pre ++ NT x :: suf) g).
      { left; eauto. }
      apply Ht in Hl; apply Ht in Hl'; auto.
      rewrite Hl in Hl'.
      inv Hl'; auto. }
    apply medial in Heq.
    destruct Heq.
    + eapply Lemmas.no_first_follow_conflicts; eauto.
      * eapply nullable_sym_in; eauto.
      * eapply follow_pre; eauto.
        apply FirstGamma with (gpre := []) (s := NT x); eauto.
    + destruct H1.
      * eapply Lemmas.no_first_follow_conflicts with (sym := NT x); eauto.
        -- eapply nullable_sym_in with (gamma := gpre); auto.
        -- eapply follow_pre with (pre := gpre); eauto.
           apply FirstGamma with (gpre := []); auto.
      * subst; eauto.
Qed.
Print Assumptions no_direct_left_recursion_in_LL1_first'.

Lemma no_direct_left_recursion_in_LL1_first :
  forall g t la x pre suf,
    parse_table_for t g
    -> first_sym g la (NT x)
    -> nullable_gamma g pre
    -> ~ In (x, pre ++ NT x :: suf) (productions g).
Proof.
  unfold not; intros.
  eapply no_direct_left_recursion_in_LL1_first'; eauto.
Qed.

Lemma no_direct_left_recursion_in_LL1_follow' :
  forall g t la x gamma sym,
    parse_table_for t g
    -> In (x, gamma) (productions g)
    -> nullable_gamma g gamma
    -> follow_sym g la sym
    -> forall pre suf,
        sym = NT x
        -> nullable_gamma g pre
        -> In (x, pre ++ NT x :: suf) (productions g)
        -> lookahead_for la x (pre ++ NT x :: suf) g
        -> False.
Proof.
  intros g t la x gamma sym Ht Hi Hn Hf.
  intros; subst.
  
  induction Hf.
  - intros pre suf He Hn' Hi'; subst; inv He.
    
    
  intros.
  assert ( gamma = pre ++ NT x :: gamma).
  { 
  assert (
  induction Hf.
  - intros pre suf Hn' Hi'; subst.
    
    
    
  
Lemma lr_not_ll1_first_direct :
  forall g t la sym,
    parse_table_for t g
    -> first_sym g la sym
    -> forall x pre suf,
        sym = NT x
        -> ~ In (x, pre ++ NT x :: suf) (productions g).
Proof.
  intros g t la sym Ht Hf.
  induction Hf; intros x' pre suf He; unfold not; intros Hi; subst; inv He.
  assert (gpre ++ s :: gsuf = pre ++ NT x' :: suf) by admit.
  apply medial in H1.
  destruct H1.
  - admit.
  - destruct H1.
    + admit.
    + eapply IHHf; eauto.
  
    -> forall x la pre suf gamma,
      In (x, pre ++ NT x :: suf) (productions g)
      -> nullable_gamma g gamma
      -> first_gamma g la (pre ++ NT x :: suf)
      -> False.
Proof.
  intros.
  apply fg_fg' in H2.
  induction H2.
  - 

Lemma lr_not_ll1_first :
  forall g t la x z,
    parse_table_for t g
    -> nullable_path g la x z
    -> x <> z.
Proof.
  intros g t la x z Ht Hn.
  inv Hn; unfold not; intros; subst.
  - destruct H2.
    + admit.
  - assert (exists pre' sym' suf', In (y, pre' ++ sym' :: suf') (productions g) /\ nullable_gamma g pre' /\ lookahead_for la y (pre' ++ sym' :: suf') g).
    { admit. }
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H4.
    rename x into pre'.
    rename x1 into suf'.
    rename x0 into sym'.
    assert (pre ++ NT y :: suf = pre' ++ sym' :: suf').
    { admit. }
    rewrite <- H6 in H0.
    admit.

    
    pose proof H5 as H'.
    apply medial in H5.
    destruct H5.
    + rewrite <- H' in H0.
      admit.
    + destruct H4.
      * rewrite H' in 
    + destruct H4.
      * 
      * 

Lemma lr_not_ll1 :
  forall g t la sym,
    parse_table_for t g
    -> first_sym g la sym
    -> forall x pre suf,
        sym = NT x
        -> nullable_gamma g pre
        -> In (x, pre ++ sym :: suf) (productions g)
        -> False.
Proof.
  intros g t la sym Ht Hf x pre suf He Hn Hi.
  subst.
  apply nt_first_exists in Hf.
  destruct Hf as [pre' [sym' [suf' [Hi' [Hn' [Hf' Hneq]]]]]].
  assert (pre' ++ sym' :: suf' = pre ++ NT x :: suf) by admit.
  apply medial in H.
  destruct H.
  - pose proof H as H'.
    eapply follow_pre in H; eauto.
    + eapply Lemmas.no_first_follow_conflicts; eauto.
      eapply nullable_sym_in; eauto.
    + apply fg_fg'.
      apply fg_hd.
      econstructor; eauto.
  - destruct H.
    + pose proof H as H'.
      assert (first_sym g la (NT x)); eauto.
      eapply follow_pre in H; eauto.
      * eapply Lemmas.no_first_follow_conflicts; eauto.
        eapply nullable_sym_in.
        -- apply Hn'.
        -- auto.
      * apply fg_fg'.
        apply fg_hd; auto.
    + congruence.
Admitted.

Lemma lr_not_ll1_direct_first :
  forall g t la x pre suf,
    parse_table_for t g
    -> first_sym g la (NT x)
    -> nullable_gamma g pre
    -> ~ In (x, pre ++ NT x :: suf) (productions g).
Proof.
  intros g t la x pre suf Ht Hf Hn; unfold not; intros Hi.
  - eapply lr_not_ll1; eauto.
Qed.

Lemma lr_not_ll1' :
  forall g t la x y,
    parse_table_for t g
    -> nullable_path g la x y
    -> forall sym pre suf,
        first_sym g la sym
        -> sym = NT x
        -> x = y
        -> nullable_gamma g pre
        -> In (x, pre ++ sym :: suf) (productions g)
        -> False.
Proof.
  intros.
  induction H0; subst.
  - eapply lr_not_ll1_direct_first; eauto.
  - eapply lr_not_ll1_direct_first; info_eauto.
Qed.

Lemma lr_not_ll1'' :
  forall g t la x y,
    parse_table_for t g
    -> nullable_path g la x y
    -> forall sym,
        first_sym g la sym
        -> sym = NT x
        -> x = y      
        -> False.
Proof.
  intros g t la x y Ht Hn.
  induction Hn; intros sym Hf He He'; subst.
  - eapply lr_not_ll1_direct_first; eauto.
  - inv Hf.
    assert (pre ++ NT y :: suf = gpre ++ s :: gsuf) by admit.
    apply medial in H0.
    destruct H0.
    + inv Hn.
      * admit.
      * 
    
    inv Hn.
    + admit.
    + inv Hf.
      

    inv Hf.
    assert (pre ++ NT y :: suf = gpre ++ s :: gsuf) by admit.
    + apply medial in H0.
      destruct H0.
      * 
    

    destruct (NT_as_DT.eq_dec y z).
    + subst.
      eapply IHHn; eauto.
    + inv Hn.
      * 
  
  induction Hf; intros x' He; unfold not; intros Hn; subst.
  - inv He.
  - inv He.
    rename x' into x.
    destruct s as [y | x'].
    + clear IHHf.
      inv Hf.
    
    inv Hn.
    + eapply lr_not_ll1_direct_first; eauto.
    + 
    eapply IHHf; eauto.
  
Proof.
  
Lemma null_path_not_ll1_first :
  forall g t la x y,
    parse_table_for t g
    -> nullable_path g la x y
    -> forall sym,
        first_sym g la sym
        -> sym = NT x
        -> x = y
        -> False.
Proof.
  intros g t la x y Ht Hn.
  induction Hn; intros; subst.
  - eapply lr_not_ll1_direct_first; eauto.
  - inv H3.
    assert (pre ++ NT y :: suf = gpre ++ s :: gsuf) by admit.
    apply medial in H0.
    destruct H0.
    + 

    eapply IHHn; eauto.
  i
    -> nullable_gamma g pre
    -> ~ In (x, pre ++ NT x :: suf) (productions g).



    -> forall x pre suf,
        sym = NT x
        -> nullable_gamma g pre
        -> In (x, pre ++ sym :: suf) (productions g)
        -> False.
Proof.

Lemma lr_not_ll1' :
  forall g t la x y,
    parse_table_for t g
    -> nullable_path g la x y
    -> forall sym pre suf,
        first_sym g la sym
        -> sym = NT x
        -> x = y
        -> nullable_gamma g pre
        -> In (x, pre ++ sym :: suf) (productions g)
        -> False.
Proof.
  intros g t la x y Ht Hn.
  inv Hn; intros sym pre' suf' Hf He He' Hn' Hi; subst.
  - admit.
  - admit. inv Hf.
    assert ((pre ++ NT y :: suf) = (gpre ++ s :: gsuf)) by admit.
    apply medial in H0.
    destruct H0.
    + 
    
Lemma lr_not_ll1' :
  forall g tbl la x y,
    parse_table_for tbl g
    -> nullable_path g la x y
    -> x = y
    -> False.
Proof.
  intros g tbl la x y Ht Hn.
  induction Hn; intros; subst.
  - rename z into x.
    admit.
  - rename z into x.
    assert (nullable_path g la x y).
    { eapply DirectPath; eauto. }
    
    + 
    destruct H2.
    + inv H0.
      rewrite <- H2 in H.
      assert (first_sym g la (NT x)).
      { econstructor; eauto. }
      apply nt_first_exists in H0.
      destruct H0 as [pre' [sym' [suf' [Hin [Hng [Hfs Hneq]]]]]].
      rewrite H2 in H.
      assert (pre ++ NT x :: suf = pre' ++ sym' :: suf').
      { admit. }
      apply Hneq.
      
      destruct pre; destruct pre'; simpl in *.
      * inv H0; auto.
      * inv H0.
        admit.
      * inv H0.
        admit.
      * inv H0.
        
  inv Hn.
  - rename y into x.
    destruct H2.
    + inv H0.
      rewrite <- H2 in H.
      
    apply Ht in H2; auto.
    
  revert He.
  induction Hn; intros; subst.
  - admit.
  - apply IHHn; clear IHHn.
    
  
Lemma foo :
  forall g t la sym,
    parse_table_for t g
    -> first_sym g la sym
    -> forall x pre suf,
        sym = NT x
        -> In (x, pre ++ sym :: suf) (productions g)
        -> nullable_gamma g pre
        -> False.
Proof.
  intros g t la sym Ht Hf.
  induction Hf as [y | x' pre' sym' suf' la Hi' Hn' Hf' IH]; intros x pre suf He Hi Hn; subst.
  - inv He.
  - inv He.
    destruct sym' as [y | x'].
    + inv Hf'.
      assert (Hl : lookahead_for (LA y) x (pre ++ NT x :: suf) g).
      { left; eauto. }
      assert (Hl' : lookahead_for (LA y) x (pre' ++ T y :: suf') g).
      { left; auto. }
      apply Ht in Hl; apply Ht in Hl'; auto.
      pose proof Hl' as Hl''.
      rewrite Hl in Hl'; inv Hl'.
      
      destruct pre; destruct pre'; simpl in *.
      * inv H0.
      * inv H0.
        admit.
      * inv H0.
        inv Hn.
        inv H1.
      * 
      
    eapply IH; clear IH; eauto.
    assert (Hl : lookahead_for la x (pre ++ NT x :: suf) g).
    { left; eauto. }
    assert (Hl' : lookahead_for la x (pre' ++ sym' :: suf') g).
    { left; auto. }
    apply Ht in Hl; apply Ht in Hl'; auto.
    rewrite Hl in Hl'; inv Hl'; clear Hl.
    destruct pre; destruct pre'; simpl in *.
    + inv H0; auto.
    + inv H0.
      inv Hn'.
      admit.
    + inv H0.
      inv Hn.
      admit.
    + inv Hn.
      
    
    unfold not in *.
    inv Hf'.
    + admit.
    + eapply IH; eauto.
      
    eapply IH; eauto.
    
    assert (Hl : lookahead_for la x (pre ++ NT x :: suf) g).
    { left; eauto. }
    assert (Hl' : lookahead_for la x (pre' ++ sym' :: suf') g).
    { left; auto. }
    apply Ht in Hl; apply Ht in Hl'; auto.
    rewrite Hl in Hl'; clear Hl.
    inv Hl'.
    rewrite <- H0 in Hi'.
    inv Hf'.
    + admit.
    + 
    eapply IH in Hi'.
    destruct pre; simpl in *.
    + destruct pre'; simpl in *.
      * inv H0; auto.
      * inv H0.
        admit.
    + destruct pre'; simpl in *.
      * inv H0.
        admit.
      * inv H0.
      
      constructor; auto.
      
    con}
    inv Hf'.
    apply IH in Hi'; auto.
    apply Hi'.
    apply IH; clear IH.
    + assert (lookahead_for la x (pre ++ NT x :: suf) g).
      { left; eauto. }
      assert (lookahead_for la x (gpre ++ s :: gsuf) g).
      { left; auto. }
      apply Ht in H1; apply Ht in H2; auto.
      rewrite H1 in H2.
      inv H2.
      destruct pre; destruct gpre; simpl in *.
      * inv H4; auto.
      * inv H4. 
      
        constructor; auto.
        econstructor; eauto.
    + 
  
Hi : In (x, gpre ++ s :: gsuf) (productions g)
  Hn : nullable_gamma g pre
  H0 : nullable_gamma g gpre
  H2 : first_sym g la s
  H : gpre ++ s :: gsuf = pre ++ NT x :: suf
  ============================
  False

Lemma l :
  forall g t x pre suf la,
    parse_table_for t g
    -> In (x, pre ++ NT x :: suf) (productions g)
    -> nullable_gamma g pre
    -> first_gamma g la (pre ++ NT x :: suf)
    -> False.
Proof.
  intros g t x pre suf la Ht Hi Hn Hf.
  inv Hf.
  rewrite <- H in Hi.
     
  revert H.
  induction H2.
  - admit.
  - intros.
  


Lemma l :
  forall t g x pre suf la,
    parse_table_for t g
    -> In (x, pre ++ NT x :: suf) (productions g)
    -> nullable_gamma g pre
    -> lookahead_for la x (pre ++ NT x :: suf) g
    -> False.
Proof.
  intros t g x pre suf la Ht Hin Hng Hlf.
  destruct Hlf.
  - inv H.
    rewrite <- H0 in Hin.
    
    pose proof Hin as Hin'.
    rewrite <- H0 in Hin'.
    induction H3.
    + destruct gpre; destruct pre; simpl in *; subst.
      * inv H0.
      * inv H0.
        inv Hng.
        inv H2.
      * inv H0.
        inv H1.
        
  induction pre; simpl in *.
  - inv H2.
    + inv H3.
      subst.
      rewrite <- H2 in H0.
      destruct gpre.
      * simpl in *.
        inv H2.
        
      
  - 

Lemma lr_not_ll1 :
  forall g tbl x y la,
    parse_table_for tbl g
    -> x = y
    -> ~ nullable_path g x y la.
Proof.
  intros g t x y la Ht He; unfold not; intros Hl.
  revert He.
  induction Hl as
      [x z la gamma pre suf Hin Heq Hng Hlf |
       x z la gamma y pre suf Hin Heq Hng Hlf Hnp IH]; intros; subst.
  - rename z into x.
    pose proof Hlf as Hlf'.
    destruct Hlf.
    + induction H.
      * induction H0.
        -- 

        
  - apply IH; clear IH.
    rename z into x.
    inv Hnp.
    + rename pre0 into pre'.
      rename suf0 into suf'.
      assert (lookahead_for la y (
    destruct Hlf.
    + 
    inv Hnp.
    assert (lookahead_for la y (pre ++ NT y :: suf) g).
    { 
    
  


Inductive nlr_tree_derivation (g : grammar) :
  symbol -> list string -> list nonterminal -> tree -> list string -> Prop :=
| T_nlr :
    forall (y : terminal) (vis : list nonterminal) (rem : list string),
      nlr_tree_derivation g (T y) [y] vis (Leaf y) rem
| NT_nlr :
    forall (x : nonterminal) 
           (gamma : list symbol)
           (word rem : list terminal)
           (vis : list nonterminal)
           (subtrees : list tree),
      In (x, gamma) g.(productions)
      -> lookahead_for (peek (word ++ rem)) x gamma g
      -> ~ In x vis
      -> nlr_forest_derivation g gamma word (x :: vis) subtrees rem
      -> nlr_tree_derivation g (NT x) word vis (Node x subtrees) rem
with nlr_forest_derivation (g : grammar) :
       list symbol -> list string -> list nonterminal -> list tree -> list string -> Prop :=
     | Nil_nlr : forall vis rem,
         nlr_forest_derivation g [] [] vis [] rem
     | ConsNull_nlr : forall hdSym tlSyms wsuf rem vis hdTree tlTrees,
         nlr_tree_derivation g hdSym [] vis hdTree (wsuf ++ rem)
         -> nlr_forest_derivation g tlSyms wsuf vis tlTrees rem
         -> nlr_forest_derivation g (hdSym :: tlSyms)
                                    wsuf
                                    vis
                                    (hdTree :: tlTrees)
                                    rem
     | ConsNonNull_nlr : forall hdSym tlSyms wpre wsuf rem vis hdTree tlTrees,
         wpre <> []
         -> nlr_tree_derivation g hdSym wpre vis hdTree (wsuf ++ rem)
         -> nlr_forest_derivation g tlSyms wsuf [] tlTrees rem
         -> nlr_forest_derivation g (hdSym :: tlSyms)
                                    (wpre ++ wsuf)
                                    vis
                                    (hdTree :: tlTrees)
                                    rem.
Require Import LL1.Parser.

Lemma der_func :
  forall g tbl (H : parse_table_for tbl g) sym word tr rem,
    (@sym_derives_prefix g) sym word tr rem
    -> exists vis,
    forall a,
      p2 tbl sym (word ++ rem) vis a = inr (tr, rem).
Proof.
  intros g tbl Ht sym word tr rem H.
  induction H using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) => exists vis : list nonterminal,
                forall a,
                  p2 tbl sym (word ++ rem) vis a = inr (tr, rem))
      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) => exists vis : list nonterminal,
                forall a,
                  pf2 tbl gamma (word ++ rem) vis a = inr (f, rem)).
  - eexists; intros; destruct a; simpl.
    step; tc.

  - eexists; intros; destruct a; simpl.
    step; tc.
    + apply Ht in l; auto.
      admit.
    + step.
      step; tc.
      * 
      
      (P0 := fun gamma input f rem (H : gamma_derives_prefix gamma input f rem) => exists vis : list nonterminal,
                 nlr_forest_derivation g gamma input vis f rem).
  
Lemma der_der' :
  forall g sym input tr rem,
    (@sym_derives_prefix g) sym input tr rem
    -> exists vis,
      nlr_tree_derivation g sym input vis tr rem.
Proof.
  intros.
  induction H using sdp_mutual_ind with
      (P := fun sym input tr rem (H : sym_derives_prefix sym input tr rem) => exists vis : list nonterminal,
                nlr_tree_derivation g sym input vis tr rem)

      (P0 := fun gamma input f rem (H : gamma_derives_prefix gamma input f rem) => exists vis : list nonterminal,
                nlr_forest_derivation g gamma input vis f rem).
  - eexists; constructor.
  - destruct IHsym_derives_prefix as [vis Hn].
    eexists; econstructor; eauto.
Admitted.

Lemma der'_func :
  forall g tbl sym word rem vis a tr,
    parse_table_for tbl g
    -> nlr_tree_derivation g sym word vis tr rem
    -> p2 tbl sym (word ++ rem) vis a = inr (tr, rem).
Admitted.

Definition sublist A (xs ys : list A) : Prop :=
  forall x, In x xs -> In x ys.

Lemma func_nil :
  forall tbl sym input rem vis vis' tr a a',
    p2 tbl sym input vis' a = inr (tr, rem)
    -> sublist nonterminal vis vis'
    -> p2 tbl sym input vis a' = inr (tr, rem).
Admitted.

 *)
