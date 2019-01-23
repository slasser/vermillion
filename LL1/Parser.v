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

Inductive parse_failure : Set :=
| Mismatch : string -> list string -> parse_failure
| LeftRec  : list nonterminal -> parse_failure
| Error    : parse_failure.

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

Require Import EndToEnd.


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

Definition parse_wrapper tbl sym input vis :=
  p tbl sym input vis (triple_lt_wf (meas tbl input vis (F_arg sym))).

Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (parse_wrapper tbl (NT X) ["a"] [])
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (parse_wrapper tbl (NT X) ["a"; "a"; "a"] [])
                end.

Eval compute in parse_wrapper lr_table (NT X) ["a"] [].

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

(* next steps :

   - more expressive return type (partial parse tree, left-recursive nonterminal, etc.
   - condense two match expressions in parseForest into single expression? 
   - ask about why ptlk_dec is required
 *)

