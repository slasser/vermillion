Require Import FMaps List MSets Omega String Program.Wf Arith.Wf_nat.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Utils.
Require Import Lib.Tactics.
Require Import LL1.Derivation.
Require Import LL1.Proofs.Lemmas.
Require Import LL1.ParseTable. 
Require Import LL1.ParseTableGen. (* for fromNtList *)
Import ListNotations.
Open Scope string_scope.

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

Definition meas tbl (word : list string) (vis : NtSet.t) (sa : sym_arg) :=
  (List.length word,
   NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))                                  vis),
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
    -> ~ NtSet.In x vis
    -> Acc triple_lt (meas tbl input (NtSet.add x vis) sa').
Proof.
  intros.
  eapply Acc_inv; eauto.
  unfold meas.
  apply snd_lt; simpl.
  apply NP.subset_cardinal_lt with (x := x); try ND.fsetdec.
  apply in_A_not_in_B_in_diff; auto.
  apply in_list_iff_in_fromNtList.
  eapply pt_lookup_in_nt_keys; eauto.
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

Ltac step_g_eq s := let Heq := fresh s in
                    match goal with
                    | |- context[match ?x with | _ => _ end] => destruct x eqn:Heq
                    end.

Ltac step := simpl in *; (first [step_h | step_g]); auto.
Ltac step_eq s := simpl in *; (first [step_h_eq s | step_g_eq s]); auto.
Ltac cr := repeat step.
Ltac cr_eq s := repeat (step_eq s).
Ltac tc := try congruence.

Open Scope list_scope.

Lemma l_ident_eq_nil :
  forall A (xs ys : list A), xs ++ ys = ys -> xs = [].
Proof.
  intros.
  rewrite <- app_nil_l in H.
  apply app_inv_tail in H; auto.
Qed.

Inductive parse_failure : Type :=
| Reject   : string -> list string -> parse_failure
| LeftRec  : nonterminal -> NtSet.t -> list string -> parse_failure.

Definition mem_dec (x : nonterminal) (s : NtSet.t) : {NtSet.In x s} + {~ NtSet.In x s}.
  destruct (NtSet.mem x s) eqn:Hm.
  - left.
    apply NtSet.mem_spec; auto.
  - right.
    unfold not; intros H.
    apply NtSet.mem_spec in H.
    congruence.
Defined.
  
Fixpoint parse_nf (tbl : parse_table)
                  (sym : symbol)
                  (input : list string)
                  (vis : NtSet.t)
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
      match mem_dec x vis with
      | left _ => inl (LeftRec x vis input)
      | right Hnin => 
        match parseForest_nf tbl gamma input (NtSet.add x vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
        | inl pfail => inl pfail
        | inr (sts, input') =>
          inr (Node x sts, input')
        end
      end
    end
  end
with parseForest_nf (tbl : parse_table)
                    (gamma : list symbol)
                    (input : list string)
                    (vis : NtSet.t)
                    (a : Acc triple_lt (meas tbl input vis (G_arg gamma)))
         {struct a}
         : sum parse_failure (list tree * list string) :=
       match gamma as g return gamma = g -> _  with
       | nil => fun _ => inr (nil, input)
       | sym :: gamma' => fun Hg => 
                            match parse_nf tbl sym input vis (hole2 _ _ _ _ _ a) with
                            | inl pfail => inl pfail
                            | inr (lSib, input') =>
                              match Compare_dec.lt_dec (List.length input') (List.length input) with
                              | left Hlt =>
                                match parseForest_nf tbl gamma' input' NtSet.empty (hole3 _ _ _ _ _ _ _ a Hlt) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              | right Hnlt =>
                                match parseForest_nf tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                                | inl pfail => inl pfail
                                | inr (rSibs, input'') =>
                                  inr (lSib :: rSibs, input'')
                                end
                              end
                            end
       end eq_refl.

Definition parse_wrapper tbl sym input :=
  parse_nf tbl sym input NtSet.empty (triple_lt_wf (meas tbl input NtSet.empty (F_arg sym))).

Lemma parse_nf_eq_body :
  forall tbl sym input vis a,
    parse_nf tbl sym input vis a = 
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
      match mem_dec x vis with
      | left _ => inl (LeftRec x vis input)
      | right Hnin => 
        match parseForest_nf tbl gamma input (NtSet.add x vis) (hole1 _ _ _ _  _ _ _ a Hlk Hnin) with
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

