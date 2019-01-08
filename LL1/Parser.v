Require Import FMaps List MSets String Program.Wf Arith.Wf_nat.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Utils.
Require Import Lib.Tactics.
Require Import LL1.ParseTable. 
Require Import LL1.ParseTableGen. (* for fromNtList *)
Import ListNotations.
Open Scope string_scope.

Lemma decon :
  forall (n : nat) A R (f0 : A -> R) (fSn : A -> nat -> R),
    (fun a : A => match n with
                  | 0 => fun _ : A => f0 a
                  | S n' => fun _ : A => fSn a n'
                  end a) =
    (fun a : A => match n with
                  | 0 => f0 a
                  | S n' => fSn a n'
                  end).
Proof.
  intros.
  destruct n.
  - apply eq_refl.
  - apply eq_refl.
Qed.

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

Set Implicit Arguments.

Definition triple_lt : relation (nat * nat * bool) :=
  triple_lex nat nat bool lt lt bool_order.

Definition triple_lt_ind :=
  triple_lex_ind nat nat bool lt lt bool_order.

Lemma triple_lt_wf :
  well_founded triple_lt.
Proof.
  apply triple_lex_wf.
  - apply lt_wf.
  - apply lt_wf.
  - apply bool_order_wf.
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
Defined.

Lemma lt_trans : transitive nat lt.
Proof.
  red.
  apply Nat_as_DT.lt_trans.
Defined.

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
Defined.

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
Defined.

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
        
(* Fuel-less LL(1) parser defined with Program Fixpoint,
   termination proof handled separately from function definition *)
Program Fixpoint parse1 (tbl     : parse_table)
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
            match parse1 tbl (word, x :: vis, G_arg gamma) with
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
        match parse1 tbl (word, vis, F_arg sym) with
        | inl pf => inl pf
        | inr (inl (_, _)) => inl Error
        | inr (inr (lSib, exist _ tri' _)) =>
          match parse1 tbl tri' with
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
   - add Acc arg  (* done! *)
   - replace refine-generated termination proofs with lemmas (* done! *)
   - see if Function can generate correct rewriting lemma (* done -- it can't *)
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
Defined.

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
Defined.

Lemma triple_le_refl :
  forall tbl tri word vis sa,
    tri = (word, vis, sa)
    -> triple_le (meas tbl (word, vis, sa)) (meas tbl tri).
Proof.
  intros; subst.
  right; auto.
Defined.

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
Defined.

Lemma acc_vis_add :
  forall tbl tri word vis sa sym x gamma,
    tri = (word, vis, sa)
    -> sa = F_arg sym
    -> ~ In x vis
    -> pt_lookup x (peek word) tbl = Some gamma
    -> Acc triple_lt (meas tbl tri)
    -> Acc triple_lt (meas tbl (word, x :: vis, G_arg gamma)).
Proof.
  intros; subst; simpl.
  eapply Acc_inv; eauto.
  apply snd_lt.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec.
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.

(* to do : more hypotheses than needed, probably *)
Lemma if_acc_gamma_then_acc_sym :
  forall tbl tri word vis sa gamma sym gamma',
    Acc triple_lt (meas tbl tri)
    -> tri = (word, vis, sa)
    -> sa = G_arg gamma
    -> gamma = sym :: gamma'
    -> Acc triple_lt (meas tbl (word, vis, F_arg sym)).
Proof.
  intros; subst; simpl.
  eapply Acc_inv; eauto.
  apply thd_lt.
  red; eauto.
Defined.

Lemma acc_triple_lt_trans :
  forall tbl tri word vis sa gamma sym gamma' tri',
  Acc triple_lt (meas tbl tri)
  -> tri = (word, vis, sa)
  -> sa = G_arg gamma
  -> gamma = sym :: gamma'
  -> triple_lt (meas tbl tri') (meas tbl (word, vis, F_arg sym))
  -> Acc triple_lt (meas tbl tri').
Proof.
  intros; subst; simpl in *.
  eapply Acc_inv; eauto.
  eapply triple_lt_trans; eauto.
  apply thd_lt.
  red; auto.
Defined.

(* Fuel-less LL(1) parser defined with refine instead of Program Fixpoint,
   termination proof handled separately from function definition *)
Fixpoint parse2 (tbl     : parse_table)
         (tri     : list string * list nonterminal * sym_arg)
         (a : Acc triple_lt (meas tbl tri))
         {struct a}
  : sum parse_failure
        (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl tri)})
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl tri)})).
  refine (match tri as tri' return tri = tri' -> _ with
          | (word, vis, sa) =>
            fun Htri => match sa as sa' return sa = sa' -> _ with
                        | F_arg sym =>
                          (* morally, a call to parse *)
                          fun Hsa => match sym with
                                   | T y  => match word as w return word = w -> _ with
                                             | [] => fun _ => inl (Mismatch "error message" word)
                                             | token :: word' =>
                                               if beqString y token then
                                                 fun Hword =>
                                                   inr (inr (Leaf y, exist _ (word', nil, sa) _))
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
                                         fun Hlk => match parse2 tbl (word, x :: vis, G_arg gamma) _ with
                                                    | inl pf => inl pf
                                                    | inr (inr (_, _)) => inl Error
                                                    | inr (inl (sts, exist _ tri' Htri')) =>
                                                      inr (inr (Node x sts, exist _ tri' _))
                                                    end
                                       end eq_refl
                                     end
                                   end
                        | G_arg gamma =>
                          (* a call to parseForest *)
                          fun Hsa => match gamma as g return gamma = g -> _ with
                                     | nil =>
                                       fun _ => inr (inl (nil, exist _ (word, vis, sa) _))
                                     | sym :: gamma' =>
                                       fun Hgamma => match parse2 tbl (word, vis, F_arg sym) _ with
                                                     | inl pf => inl pf
                                                     | inr (inl (_, _)) => inl Error
                                                     | inr (inr (lSib, exist _ tri' Htri')) =>
                                                       match parse2 tbl tri' _ with
                                                       | inl pf => inl pf
                                                       | inr (inr (_, _)) => inl Error
                                                       | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                         inr (inl (lSib :: rSibs, exist _ tri'' _))
                                                       end
                                                     end
                                     end eq_refl
                        end eq_refl
          end eq_refl).
  - eapply tail_lt_word; eauto.
  - eapply acc_vis_add; eauto.
  - apply (vis_lt_add tri' Htri Hnin Hlk Htri').
  - eapply triple_le_refl; eauto.
  - eapply if_acc_gamma_then_acc_sym; eauto.
  - eapply acc_triple_lt_trans; eauto.
  - eapply (pf_lt_args _ _ Htri Hsa Hgamma Htri' Htri''); eauto.
Defined.
  
(* Fuel-less LL(1) parser with termination proof "inlined" *)
Fixpoint parse3 (tbl     : parse_table)
         (tri     : list string * list nonterminal * sym_arg)
         (a : Acc triple_lt (meas tbl tri))
         {struct a}
  : sum parse_failure
        (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl tri)})
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl tri)})) :=
  match tri as tri' return tri = tri' -> _ with
  | (word, vis, sa) =>
    fun Htri => match sa as sa' return sa = sa' -> _ with
                | F_arg sym =>
                  (* morally, a call to parse *)
                  fun Hsa => match sym with
                             | T y  => match word as w return word = w -> _ with
                                       | [] => fun _ => inl (Mismatch "error message" word)
                                       | token :: word' =>
                                         if beqString y token then
                                           fun Hword =>
                                             inr (inr (Leaf y, exist _ (word', nil, sa) (tail_lt_word tbl _ _ Htri Hword)))
                                         else
                                           fun _ => inl (Mismatch "error message" word)
                                       end (eq_refl _)
                             | NT x =>
                               match List.in_dec NT_as_DT.eq_dec x vis with
                               | left _ => inl (LeftRec (x :: vis))
                               | right Hnin => 
                                 match pt_lookup x (peek word) tbl as H return  pt_lookup x (peek word) tbl = H -> _ with
                                 | None => fun _ => inl (Mismatch "error message" word)
                                 | Some gamma =>
                                   fun Hlk => match parse3 tbl (word, x :: vis, G_arg gamma) (acc_vis_add tbl x Htri Hsa Hnin Hlk a) with
                                              | inl pf => inl pf
                                              | inr (inr (_, _)) => inl Error
                                              | inr (inl (sts, exist _ tri' Htri')) =>
                                                inr (inr (Node x sts, exist _ tri' (vis_lt_add tri' Htri Hnin Hlk Htri')))
                                              end
                                 end (eq_refl _)
                               end
                             end
                | G_arg gamma =>
                  (* a call to parseForest *)
                  fun Hsa => match gamma as g return gamma = g -> _ with
                             | nil =>
                               fun _ => inr (inl (nil, exist _ (word, vis, sa) (triple_le_refl tbl Htri)))
                             | sym :: gamma' =>
                               fun Hgamma => match parse3 tbl (word, vis, F_arg sym) (if_acc_gamma_then_acc_sym tbl a Htri Hsa Hgamma) with
                                             | inl pf => inl pf
                                             | inr (inl (_, _)) => inl Error
                                             | inr (inr (lSib, exist _ tri' Htri')) =>
                                               match parse3 tbl tri' (acc_triple_lt_trans tri' a Htri Hsa Hgamma Htri') with
                                               | inl pf => inl pf
                                               | inr (inr (_, _)) => inl Error
                                               | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                 inr (inl (lSib :: rSibs, exist _ tri'' (pf_lt_args _ _ Htri Hsa Hgamma Htri' Htri'')))
                                               end
                                             end
                             end (eq_refl _)
                end (eq_refl _)
  end (eq_refl _).

Definition ptlk_dec x la tbl : sum (pt_lookup x la tbl = None) {gamma | pt_lookup x la tbl = Some gamma}.
  destruct (pt_lookup x la tbl) eqn:Hlk.
  - right.
    econstructor; eauto.
  - left.
    auto.
Defined.
    
Fixpoint parse4 (tbl     : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         (a       : Acc triple_lt (meas tbl (word, vis, sa)))
         {struct a}
  : sum parse_failure
        (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl (word, vis, sa))})
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl (word, vis, sa))})).
  refine (match sa as sa' return sa = sa' -> _ with
          | F_arg sym =>
            fun Hsa => match sym with
                       | T y  => match word as w return word = w -> _ with
                                 | [] => fun _ => inl (Mismatch "error message" word)
                                 | token :: word' =>
                                   if beqString y token then
                                     fun Hword =>
                                       inr (inr (Leaf y, exist _ (word', nil, sa) _))
                                   else
                                     fun _ => inl (Mismatch "error message" word)
                                 end eq_refl
                       | NT x =>
                         match List.in_dec NT_as_DT.eq_dec x vis with
                         | left _ => inl (LeftRec (x :: vis))
                         | right Hnin =>
                           match ptlk_dec x (peek word) tbl with
                           | inl _ => inl (Mismatch "error message" word)
                           | inr (exist _ gamma Hlk) =>
                           (*match pt_lookup x (peek word) tbl as H return pt_lookup x (peek word) tbl = H -> _ with
                           | None => fun _ => inl (Mismatch "error message" word)
                           | Some gamma => *)
                             match parse4 tbl word (x :: vis) (G_arg gamma) _ with (*word (x :: vis) (G_arg gamma) a with *)
                                        | inl pf => inl pf
                                        | inr (inr _) => inl Error
                                        | inr (inl (sts, exist _ tri' Htri')) =>
                                          inr (inr (Node x sts, exist _ tri' _))
                                        end
                           end
                         end
                       end
          | G_arg gamma =>
            fun Hsa => match gamma as g return gamma = g -> _ with
                       | nil =>
                         fun _ => inr (inl (nil, exist _ (word, vis, sa) _))
                       | sym :: gamma' =>
                         fun Hgamma => match parse4 tbl word vis (F_arg sym) _ with (* tbl word vis F_arg sym (if_acc_gamma_then_acc_sym tbl a _ Hsa Hgamma) with *)
                                       | inl pf => inl pf
                                       | inr (inl _) => inl Error
                                       | inr (inr (lSib, exist _ tri' Htri')) =>
                                         match tri' as tri'2 return tri' = tri'2 -> _ with
                                         | (word', vis', _) =>
                                           fun Htri'eq => match parse4 tbl word' vis' (G_arg gamma') _ with (* tbl word' vis' (G_arg gamma') (acc_triple_lt_trans _ a _ Hsa Hgamma Htri') with*)
                                                          | inl pf => inl pf
                                                          | inr (inr _) => inl Error
                                                          | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                            inr (inl (lSib :: rSibs, exist _ tri'' _))
                                                          end
                                         end eq_refl
                                       end
                       end eq_refl
          end eq_refl).
  - eapply tail_lt_word; eauto.
  - eapply acc_vis_add; eauto.
  - eapply vis_lt_add; eauto.
  - eapply triple_le_refl; eauto.
  - eapply if_acc_gamma_then_acc_sym; eauto.
  - subst.
    inv Htri'.
    + eapply Acc_inv; eauto.
      apply fst_lt; auto.
    + simpl.
      subst.
      eapply Acc_inv; eauto.
      simpl.
      rewrite H3.
      apply snd_lt; auto.
    + inv H0.
      congruence.
  - subst.
    inv Htri'.
    + eapply pf_lt_args; eauto.
      apply fst_lt; auto.
    + eapply pf_lt_args; eauto.
      simpl.
      rewrite H3.
      apply snd_lt; auto.
    + inv H0.
      congruence.
Defined.

Definition isLeft (A B : Type) (e : sum A B) : bool :=
  match e with
  | inl _ => true
  | inr _ => false
  end.

Definition isRight (A B : Type) (e : sum A B) : bool :=
  negb (isLeft e).

Lemma sym_ret_inr :
  forall (tbl : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         e,
    parse4 (triple_lt_wf (meas tbl (word, vis, sa))) = inr e
    -> forall (sym : symbol),
      sa = F_arg sym
      -> isRight e = true.
Proof.
  intros; subst; simpl in *.
  destruct sym.
  - destruct word.
    + congruence.
    + destruct (beqString t s) eqn:Hbeq.
      * inv H.
        auto.
      * inv H.
  - destruct (in_dec ND.F.eq_dec n vis).
    + inv H.
    + destruct (ptlk_dec n (peek word) tbl). 
      * congruence.
      * destruct s as [gamma Hlk].
        repeat match goal with
               | H : context[match ?X with
                             | _ => _
                             end] |- _ =>
                 destruct X
               end.
        -- congruence.
        -- inv H.
           auto.
        -- congruence.
Qed.
  (* Alright! We're able to simplify a parser application in a proof setting *)

(* Goal: lemma-tize the previous function so that I can inline the termination proofs *)

Lemma hole1 :
  forall tbl token word' vis vis' sa sa',
    triple_lt (meas tbl (word', vis', sa')) (meas tbl (token :: word', vis, sa)).
Proof.
  intros.
  apply fst_lt.
  auto.
Defined.

Lemma hole2 :
  forall tbl word vis sa sa' x gamma ,
    Acc triple_lt (meas tbl (word, vis, sa))
    -> ~ In x vis
    -> pt_lookup x (peek word) tbl = Some gamma
    -> Acc triple_lt (meas tbl (word, x :: vis, sa')).
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply snd_lt; simpl.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec. 
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.

Lemma hole3 :
  forall tbl word vis sa sa' tri' x gamma,
  ~ In x vis
  -> pt_lookup x (peek word) tbl = Some gamma
  -> triple_le (meas tbl tri') (meas tbl (word, x :: vis, sa'))
  -> triple_lt (meas tbl tri') (meas tbl (word, vis, sa)).
Proof.
  intros.
  eapply triple_le_lt_trans; eauto.
  apply snd_lt; simpl.
  (* to do: factor out this part *)
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec. 
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.

Lemma hole4 :
  forall tbl word vis sa,
    triple_le (meas tbl (word, vis, sa)) (meas tbl (word, vis, sa)).
Proof.
  intros.
  right; auto.
Defined.

Lemma hole5 :
  forall tbl word vis sa sym gamma,
  Acc triple_lt (meas tbl (word, vis, sa))
  -> sa = G_arg gamma
  -> Acc triple_lt (meas tbl (word, vis, F_arg sym)).
Proof.
  intros; subst.
  eapply Acc_inv; eauto.
  apply thd_lt; red; auto.
Defined.

Lemma hole6 :
  forall tbl word vis sa gamma sym gamma' tri' word' vis' sa',
  Acc triple_lt (meas tbl (word, vis, sa))
  -> sa = G_arg gamma
  -> triple_lt (meas tbl tri') (meas tbl (word, vis, F_arg sym))
  -> tri' = (word', vis', sa')
  -> Acc triple_lt (meas tbl (word', vis', G_arg gamma')).
Proof.
  intros tbl word vis sa gamma sym gamma' tri' word' vis' sa' Ha Hsa Hlt Htri'; subst; simpl in *.
  eapply Acc_inv; eauto.
  inv Hlt.
  - apply fst_lt; auto.
  - assert (H : List.length word' = List.length word) by auto.
    rewrite H.
    apply snd_lt; auto.
  - exfalso.
    (* LEMMA *)
    destruct sa'.
    + simpl in *.
      red in H0.
      destruct H0.
      congruence.
    + simpl in *.
      red in H0.
      destruct H0.
      congruence.
Defined.

Lemma hole7 :
  forall tbl word word' vis vis' sa sa' tri' tri'' sym gamma,
    triple_le (meas tbl tri'') (meas tbl (word', vis', G_arg gamma))
    -> triple_lt (meas tbl tri') (meas tbl (word, vis, F_arg sym))
    -> tri' = (word', vis', sa')
    -> triple_le (meas tbl tri'') (meas tbl (word, vis, sa)).
Proof.
  intros; subst.
  left.
  destruct H.
  - eapply triple_lt_trans; eauto.
    inv H0.
    + apply fst_lt; auto.
    + assert (Hl : List.length word' = List.length word) by auto.
      simpl.
      rewrite Hl.
      apply snd_lt; auto.
    + exfalso.
      destruct sa'.
      * simpl in *; red in H2; destruct H2; congruence.
      * simpl in *; red in H2; destruct H2; congruence.
  - rewrite H.
    (* LEMMA *)
    inv H0.
    + apply fst_lt; auto.
    + assert (Hl : List.length word' = List.length word) by auto.
      simpl.
      rewrite Hl.
      apply snd_lt; auto.
    + exfalso.
      destruct sa'.
      * simpl in *; red in H2; destruct H2; congruence.
      * simpl in *; red in H2; destruct H2; congruence.
Defined.
  
Fixpoint parse5 (tbl     : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         (a       : Acc triple_lt (meas tbl (word, vis, sa)))
         {struct a}
  : sum parse_failure
        (sum (list tree * {tri' | triple_le (meas tbl tri') (meas tbl (word, vis, sa))})
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl (word, vis, sa))})).
  refine (match sa as sa' return sa = sa' -> _ with
          | F_arg sym =>
            fun Hsa => match sym with
                       | T y  => match word as w return word = w -> _ with
                                 | [] => fun _ => inl (Mismatch "error message" word)
                                 | token :: word' =>
                                   if beqString y token then
                                     fun Hword =>
                                       inr (inr (Leaf y, exist _ (word', nil, sa) (hole1 _ _ _ _ _ _ _)))
                                   else
                                     fun _ => inl (Mismatch "error message" word)
                                 end eq_refl
                       | NT x =>
                         match List.in_dec NT_as_DT.eq_dec x vis with
                         | left _ => inl (LeftRec (x :: vis))
                         | right Hnin =>
                           match ptlk_dec x (peek word) tbl with
                           | inl _ => inl (Mismatch "error message" word)
                           | inr (exist _ gamma Hlk) =>
                             (* Why do I need these two wildcards? *)
                             match parse5 tbl word (x :: vis) (G_arg gamma) (hole2 _ _ a Hnin Hlk) with 
                                        | inl pf => inl pf
                                        | inr (inr _) => inl Error
                                        | inr (inl (sts, exist _ tri' Htri')) =>
                                          inr (inr (Node x sts, exist _ tri' (hole3 _ _ Hnin Hlk Htri')))
                                        end
                           end
                         end
                       end
          | G_arg gamma =>
            fun Hsa => match gamma as g return gamma = g -> _ with
                       | nil =>
                         fun _ => inr (inl (nil, exist _ (word, vis, sa) (hole4 _ _ _ _)))
                       | sym :: gamma' =>
                         fun Hgamma => match parse5 tbl word vis (F_arg sym) (hole5 _ a Hsa) with (* tbl word vis F_arg sym (if_acc_gamma_then_acc_sym tbl a _ Hsa Hgamma) with *)
                                       | inl pf => inl pf
                                       | inr (inl _) => inl Error
                                       | inr (inr (lSib, exist _ tri' Htri')) =>
                                         match tri' as tri'2 return tri' = tri'2 -> _ with
                                         | (word', vis', _) =>
                                           fun Htri'eq => match parse5 tbl word' vis' (G_arg gamma') (hole6 _ a Hsa Htri' Htri'eq) with (* tbl word' vis' (G_arg gamma') (acc_triple_lt_trans _ a _ Hsa Hgamma Htri') with*)
                                                          | inl pf => inl pf
                                                          | inr (inr _) => inl Error
                                                          | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                            inr (inl (lSib :: rSibs, exist _ tri'' (hole7 _ _ Htri'' Htri' Htri'eq)))
                                                          end
                                         end eq_refl
                                       end
                       end eq_refl
          end eq_refl).
Defined.

Lemma parse5_sym_ret_inr :
  forall (tbl : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         e,
    parse5 (triple_lt_wf (meas tbl (word, vis, sa))) = inr e
    -> forall (sym : symbol),
      sa = F_arg sym
      -> isRight e = true.
Proof.
  intros; subst; simpl in *.
  destruct sym.
  - destruct word.
    + congruence.
    + destruct (beqString t s) eqn:Hbeq.
      * inv H.
        auto.
      * congruence. 
  - destruct (in_dec ND.F.eq_dec n vis).
    + congruence.
    + destruct (ptlk_dec n (peek word) tbl). 
      * congruence.
      * destruct s as [gamma Hlk].
        repeat match goal with
               | H : context[match ?X with
                             | _ => _
                             end] |- _ =>
                 destruct X
               end.
        -- congruence.
        -- inv H; auto.
        -- congruence.
Qed.
