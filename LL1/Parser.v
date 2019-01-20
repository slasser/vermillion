Require Import FMaps List MSets String Program.Wf Arith.Wf_nat.
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

Section PairLT.

  Variables (A B : Type) (ltA : relation A) (ltB : relation B).

  Inductive pair_lex : A * B -> A * B -> Prop :=
  | pr_fst_lt : forall x x' y y', ltA x x' -> pair_lex (x, y) (x', y')
  | pr_snd_lt : forall x y y', ltB y y' -> pair_lex (x, y) (x, y').

  Hint Constructors pair_lex.

  Theorem pair_lex_trans :
    transitive _ ltA -> transitive _ ltB -> transitive _ pair_lex.
  Proof.
    intros tA tB [x1 y1] [x2 y2] [x3 y3] H12 H23.
    inv H12; inv H23; eauto.
  Defined.

  Theorem pair_lex_wf :
    well_founded ltA -> well_founded ltB -> well_founded pair_lex.
  Proof.
    intros wfA wfB [x y].
    revert y.
    induction (wfA x) as [x _ IHx].
    intros y.
    induction (wfB y) as [y _ IHy].
    constructor.
    intros [x' y'] H.
    inv H; eauto.
  Defined.

End PairLT.

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
             (tree      * {tri' | triple_lt (meas tbl tri') (meas tbl (word, vis, sa))})) :=
  match sa as sa' return sa = sa' -> _ with
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
                             match parse5 (*tbl word (x :: vis) (G_arg gamma) *) (hole2 (G_arg gamma) _ a Hnin Hlk) with 
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
                         fun Hgamma => match parse5 (* tbl word vis (F_arg sym) *) (hole5 sym a Hsa) with (* tbl word vis F_arg sym (if_acc_gamma_then_acc_sym tbl a _ Hsa Hgamma) with *)
                                       | inl pf => inl pf
                                       | inr (inl _) => inl Error
                                       | inr (inr (lSib, exist _ tri' Htri')) =>
                                         match tri' as tri'2 return tri' = tri'2 -> _ with
                                         | (word', vis', _) =>
                                           fun Htri'eq => match parse5 (* tbl word' vis' (G_arg gamma') *) (hole6 gamma a Hsa Htri' Htri'eq) with (* tbl word' vis' (G_arg gamma') (acc_triple_lt_trans _ a _ Hsa Hgamma Htri') with*)
                                                          | inl pf => inl pf
                                                          | inr (inr _) => inl Error
                                                          | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                            inr (inl (lSib :: rSibs, exist _ tri'' (hole7 _ _ Htri'' Htri' Htri'eq)))
                                                          end
                                         end eq_refl
                                       end
                       end eq_refl
  end eq_refl.

Lemma foo :
  forall tbl word vis sa (a : Acc triple_lt (meas tbl (word, vis, sa))),
    parse5 a =
    match sa as sa' return sa = sa' -> _ with
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
                             match parse5 (*tbl word (x :: vis) (G_arg gamma) *) (hole2 (G_arg gamma) _ a Hnin Hlk) with 
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
                         fun Hgamma => match parse5 (* tbl word vis (F_arg sym) *) (hole5 sym a Hsa) with (* tbl word vis F_arg sym (if_acc_gamma_then_acc_sym tbl a _ Hsa Hgamma) with *)
                                       | inl pf => inl pf
                                       | inr (inl _) => inl Error
                                       | inr (inr (lSib, exist _ tri' Htri')) =>
                                         match tri' as tri'2 return tri' = tri'2 -> _ with
                                         | (word', vis', _) =>
                                           fun Htri'eq => match parse5 (* tbl word' vis' (G_arg gamma') *) (hole6 gamma a Hsa Htri' Htri'eq) with (* tbl word' vis' (G_arg gamma') (acc_triple_lt_trans _ a _ Hsa Hgamma Htri') with*)
                                                          | inl pf => inl pf
                                                          | inr (inr _) => inl Error
                                                          | inr (inl (rSibs, exist _ tri'' Htri'')) =>
                                                            inr (inl (lSib :: rSibs, exist _ tri'' (hole7 _ _ Htri'' Htri' Htri'eq)))
                                                          end
                                         end eq_refl
                                       end
                       end eq_refl
    end eq_refl.
Proof.
  intros.
  unfold parse5.
  simpl.
  destruct a. (* this is the key! *)
  auto.
Qed.
      
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

Fixpoint parse6 (tbl     : parse_table)
         (word : list string)
         (vis : list nonterminal)
         (sa : sym_arg)
         (a       : Acc triple_lt (meas tbl (word, vis, sa)))
         {struct a}
  : sum parse_failure
        (tree * {tri' | triple_lt (meas tbl tri') (meas tbl (word, vis, sa))}) :=
  match sa as sa' return sa = sa' -> _ with
  | G_arg _ => fun _ => inl Error
  | F_arg sym =>
    fun Hsa => match sym with
               | T y => match word as w return word = w -> _ with
                        | [] => fun _ => inl (Mismatch "error message" word)
                        | token :: word' =>
                          if beqString y token then
                            fun Hword =>
                              inr (Leaf y, exist _ (word', nil, sa) (hole1 _ _ _ _ _ _ _))
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
                     match parseForest6 (hole2 (G_arg gamma) _ a Hnin Hlk) with 
                     | inl pf => inl pf
                     | inr (sts, exist _ tri' Htri') =>
                       inr (Node x sts, exist _ tri' (hole3 _ _ Hnin Hlk Htri'))
                     end
                   end
                 end
               end
  end eq_refl
with parseForest6 (tbl     : parse_table)
                  (word : list string)
                  (vis : list nonterminal)
                  (sa : sym_arg)
                  (a       : Acc triple_lt (meas tbl (word, vis, sa)))
                  {struct a}
     : sum parse_failure
           (list tree * {tri' | triple_le (meas tbl tri') (meas tbl (word, vis, sa))}) :=
       match sa as sa' return sa = sa' -> _ with
       | F_arg _ => fun _ => inl Error
       | G_arg gamma =>
         fun Hsa => match gamma as g return gamma = g -> _ with
                    | nil =>
                      fun _ => inr (nil, exist _ (word, vis, sa) (hole4 _ _ _ _))
                    | sym :: gamma' =>
                      fun Hgamma => match parse6 (hole5 sym a Hsa) with
                                    | inl pf => inl pf
                                    | inr (lSib, exist _ tri' Htri') =>
                                      match tri' as tri'2 return tri' = tri'2 -> _ with
                                      | (word', vis', _) =>
                                        fun Htri'eq => match parseForest6 (hole6 gamma a Hsa Htri' Htri'eq) with
                                                       | inl pf => inl pf
                                                       | inr (rSibs, exist _ tri'' Htri'') =>
                                                         inr (lSib :: rSibs, exist _ tri'' (hole7 _ _ Htri'' Htri' Htri'eq))
                                                       end
                                      end eq_refl
                                    end
                    end eq_refl
       end eq_refl.

Lemma parse_t_ret_leaf :
  forall tbl word vis sa y (a : Acc triple_lt (meas tbl (word, vis, sa))) tr tri' pf,
    sa = F_arg (T y)
    -> parse6 a = inr (tr, exist _ tri' pf)
    -> isLeaf tr = true.
Proof.
  intros.
  unfold parse6 in H; destruct a; subst; simpl in *.
  - destruct word.
    + congruence.
    + destruct (beqString y s).
      * inv H0.
        auto.
      * congruence.
Qed.

Ltac crush :=
  repeat (simpl in *;
          match goal with
          | H : context[match ?X with | _ => _ end] |- _ =>
            let Heq := fresh "Heq" in
            destruct X eqn:Heq
          | H : inr _ = inr _ |- _ => inv H

          | H : inl _ = inr _ |- _ => congruence
          | H : isNode (Leaf _) = true |- _ => inv H
          end;
          auto).
          
Lemma parse_nt_ret_node :
  forall tbl word vis x (a : Acc triple_lt (meas tbl (word, vis, F_arg (NT x)))) tr tri' pf,
    parse6 a = inr (tr, exist _ tri' pf)
    -> isNode tr = true.
Proof.
  intros.
  destruct a.
  crush.
Qed.

(*
Require Import Lib.Lemmas.
Require Import LL1.Derivation.

Lemma parse_correct' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (input rem : list string)
              (vis vis' : list nonterminal)
              (sym   : symbol)
              (sa' : sym_arg)
              (a : Acc triple_lt (meas tbl (input, vis, F_arg sym)))
              (tr : tree)
              pf,
      parse6 a = inr (tr, exist _ (rem, vis', sa') pf)
      -> exists word,
        word ++ rem = input
        /\ (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros.
  induction tr as [ s
                  | s f IHpf
                  |
                  | tr IHp f IHpf ]
                    using tree_nested_ind with
      
      (P := fun tr =>
              parse6 a = inr (tr, exist _ (rem, vis', sa') pf)
              -> exists word : list string,
                word ++ rem = input /\ sym_derives_prefix sym word tr rem)
      
      (Q := fun f =>
              forall input rem vis vis' gamma sa' pf (a : Acc triple_lt (meas tbl (input, vis, G_arg gamma))),
                parseForest6 a = inr (f, exist _ (rem, vis', sa') pf)
                -> exists word,
                  word ++ rem = input
                  /\ gamma_derives_prefix gamma word f rem).

  - destruct a.
    destruct sym as [y | x] eqn:Hsym.
    + destruct input as [| token word'].
      * crush.
      * crush.
        exists [token]; split; auto.
        apply beqString_eq in Heq; subst.
        constructor.
    + crush.

  - destruct a.
    destruct sym as [y | x].
    + crush.
    + simpl in H0.
      destruct (in_dec ND.F.eq_dec x vis).
      * crush.
      * destruct (ptlk_dec x (peek input) tbl).
        -- crush.
        -- destruct s0 as [gamma Hlk].
           crush.
Abort.
 *)

Fixpoint pf7 (p : parse_table -> symbol -> list string -> list nonterminal -> (option tree * list string))
             (tbl : parse_table) 
             (gamma : list symbol)
             (input : list string)
             (vis : list nonterminal)
             : (option (list tree) * list string) :=
  match gamma with
  | nil => (Some nil, input)
  | sym :: gamma' =>
    match p tbl sym input vis with
    | (None, _) => (None, input)
    | (Some lSib, input') =>
      match pf7 p tbl gamma' input' [] with
      | (None, _) => (None, input)
      | (Some rSibs, input'') =>
        (Some (lSib :: rSibs), input'')
      end
    end
  end.

Definition m7 (tbl : parse_table)
              (vis : list nonterminal) :=
  NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))
                             (fromNtList vis)).

Program Fixpoint p7 (tbl : parse_table)
                    (sym : symbol)
                    (input : list string)
                    (vis : list nonterminal)
                    {measure (m7 tbl vis)}
  : (option tree * list string) :=
  match (sym, input) with
  | (T _, nil) => (None, input)
  | (T y, token :: input') =>
    if beqString y token then
      (Some (Leaf y), input')
    else
      (None, input)
  | (NT x, _) =>
    match pt_lookup x (peek input) tbl with
    | None => (None, input)
    | Some gamma =>
      if List.in_dec NT_as_DT.eq_dec x vis then
        (None, input)
      else
        let fix pf7 gamma input :=
            match gamma with
            | nil => (Some nil, input)
            | sym :: gamma' =>
              match p7 tbl sym input (x :: vis) with
              | (None, _) => (None, input)
              | (Some lSib, input') =>
                match pf7 gamma' input' with
                | (None, _) => (None, input)
                | (Some rSibs, input'') =>
                  (Some (lSib :: rSibs), input'')
                end
              end
            end
        in  match pf7 gamma input with
            | (None, _) => (None, input)
            | (Some sts, input') =>
              (Some (Node x sts), input')
            end
    end
  end.
Next Obligation.
  unfold m7; simpl.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec.
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.

Lemma p8_hole :
  forall tbl vis x input gamma,
  Acc lt (m7 tbl vis)
  -> pt_lookup x (peek input) tbl = Some gamma
  -> ~ In x vis
  -> Acc lt (m7 tbl (x :: vis)).
Proof.
  intros.
  eapply Acc_inv; eauto.
  unfold m7; simpl.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec.
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.

Fixpoint p8 (tbl : parse_table)
         (sym : symbol)
         (input : list string)
         (vis : list nonterminal)
         (a : Acc lt (m7 tbl vis))
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
        let fix pf8 gamma input :=
            match gamma with
            | nil => (Some nil, input)
            | sym :: gamma' =>
              match p8 tbl sym input (x :: vis) (p8_hole _ _ _ _ a Hlk Hnin) with
              | (None, _) => (None, input)
              | (Some lSib, input') =>
                match pf8 gamma' input' with
                | (None, _) => (None, input)
                | (Some rSibs, input'') =>
                  (Some (lSib :: rSibs), input'')
                end
              end
            end
        in  match pf8 gamma input with
            | (None, _) => (None, input)
            | (Some sts, input') =>
              (Some (Node x sts), input')
            end
      end
    end
  end.

Lemma p8_eq_body :
  forall tbl sym input vis a,
    p8 tbl sym input vis a =
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
          let fix pf8 gamma input :=
              match gamma with
              | nil => (Some nil, input)
              | sym :: gamma' =>
                match p8 tbl sym input (x :: vis) (p8_hole _ _ _ _ a Hlk Hnin) with
                | (None, _) => (None, input)
                | (Some lSib, input') =>
                  match pf8 gamma' input' with
                  | (None, _) => (None, input)
                  | (Some rSibs, input'') =>
                    (Some (lSib :: rSibs), input'')
                  end
                end
              end
          in  match pf8 gamma input with
              | (None, _) => (None, input)
              | (Some sts, input') =>
                (Some (Node x sts), input')
              end
        end
      end
    end.
Proof.
  intros.
  unfold p8.
  destruct a.
  destruct sym.
  - destruct input; auto.
  - destruct (ptlk_dec n (peek input) tbl); auto.
Qed.

Ltac dest_match :=
  repeat match goal with
         | H : context[match ?x with | _ => _ end] |- _ =>
           destruct x
         end.

Lemma p8_t_ret_leaf :
  forall tbl y word vis a tr rem,
    p8 tbl (T y) word vis a = (Some tr, rem)
    -> isLeaf tr = true.
Proof.
  intros.
  destruct a.
  rewrite p8_eq_body in H.
  dest_match; try inv H; auto.
Qed.

Lemma p8_nt_ret_node :
  forall tbl x word vis a tr rem,
    p8 tbl (NT x) word vis a = (Some tr, rem)
    -> isNode tr = true.
Proof.
  intros.
  rewrite p8_eq_body in H.
  dest_match; try inv H.
  destruct x0; simpl in *.
  - inv H1; auto.
  - dest_match; try congruence.
    subst.
    inv H1; auto.
Qed.

Require Import LL1.Derivation.  

Lemma p8_sound' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              (vis : list nonterminal)
              a,
      p8 tbl sym input vis a = (Some tr, rem)
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
      
      (P := fun tr =>
              forall (sym : symbol) (input rem : list terminal)
                     (vis : list nonterminal) (a : Acc lt (m7 tbl vis)),
                p8 tbl sym input vis a = (Some tr, rem) ->
                exists word : list terminal,
                  word ++ rem = input /\
                  sym_derives_prefix sym word tr rem)

      (Q := fun f =>
              forall gamma input rem vis a,
                (fix pf8 gamma input :=
                   match gamma with
                   | nil => (Some nil, input)
                   | sym :: gamma' =>
                     match p8 tbl sym input vis a with
                     | (None, _) => (None, input)
                     | (Some lSib, input') =>
                       match pf8 gamma' input' with
                       | (None, _) => (None, input)
                       | (Some rSibs, input'') =>
                         (Some (lSib :: rSibs), input'')
                       end
                     end
                   end) gamma input = (Some f, rem)
                -> exists word,
                  word ++ rem = input
                  /\ gamma_derives_prefix gamma word f rem).

  - intros.
    destruct sym as [y|x].
    + rewrite p8_eq_body in H.
      destruct input; try congruence.
      destruct (beqString y t) eqn:Hb; try congruence.
      inv H.
      apply beqSym_eq in Hb; subst.
      eexists; split.
      * replace (t :: rem) with ([t] ++ rem); auto.
      * constructor.
    + apply p8_nt_ret_node in H.
      inv H.

  - intros.
    destruct sym as [y|x].
    + apply p8_t_ret_leaf in H; inv H.
    + rewrite p8_eq_body in H.
      destruct (ptlk_dec x (peek input) tbl); try congruence.
      destruct s0 as [gamma Hlk].
      destruct (in_dec ND.F.eq_dec x vis); try congruence.
      progress simpl in H.
      match goal with
      | H : context[?f gamma input] |- _ =>
        destruct (f gamma input) eqn:Hpf
      end.
      destruct o; try congruence.
      inv H.
      specialize (IHpf gamma input rem (s :: vis) (p8_hole tbl vis s input a Hlk n)).
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf as [word [Happ Hd]].
      subst.
      eexists; split; eauto.
      apply Htbl in Hlk.
      destruct Hlk.
      econstructor; eauto.

  - intros.
    destruct gamma.
    + inv H.
      exists nil; split; auto.
      constructor.
    + destruct (p8 tbl s input vis a).
      * destruct o; try congruence.
        match goal with
        | H : context[?f ?a ?b] |- _ =>
          destruct (f a b)
        end.
        destruct o; try congruence.
        
  - intros.
    destruct gamma; try congruence.
    destruct (p8 tbl s input vis a) eqn:Hp.
    destruct o; try congruence.
    match goal with
    | H : context[?f ?a ?b] |- _ =>
      destruct (f a b) eqn:Hpf
    end.
    destruct o; try congruence.
    inv H.
    apply IHp in Hp; clear IHp.
    apply IHpf with (a := a) in Hpf.
    destruct Hp as [wpre [Happ Hs]].
    destruct Hpf as [wsuf [Happ' Hg]].
    subst.
    exists (wpre ++ wsuf).
    split.
    + rewrite app_assoc; auto.
    + constructor; auto.
Qed.

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

Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (p8 tbl (NT X) ["a"] [] (lt_wf (m7 tbl [])))
                end.

Definition a_generator :=
  {|
     start := X
   ; productions := [(X, [T "a"; NT X]);
                     (X, [])]
  |}.

Eval compute in parseTableOf a_generator.

(* This example shows that p8 is incomplete as written --
   a valid LL(1) parser generated with this grammar should
   accept any sequence of a's *)
Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (p8 tbl
                                       (NT X)
                                       ["a"; "a"; "a"]
                                       []
                                       (lt_wf (m7 tbl [])))
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (parse tbl
                                       (NT X)
                                       ["a"; "a"; "a"]
                                       17)
                end.

Definition lr_table :=
  ParseTable.add (X, LA "a") [NT Y; NT Z]
                 (ParseTable.add (Y, LA "a") []
                                 (ParseTable.add (Z, LA "a") [NT X]
                                                 (ParseTable.empty (list symbol)))).

Eval compute in (p8 lr_table (NT X) ["a"] [] (lt_wf (m7 lr_table []))).

Definition pair_lt := pair_lex nat nat lt lt.

Definition m9 tbl (input : list string) vis :=
  (List.length input, NtSet.cardinal
                        (NtSet.diff (fromNtList (nt_keys tbl))                                     (fromNtList vis))).

(* things to try today:

   nested recursion--inner func is structurally recursive on gamma
   + extra "lt fact" arg
   + extra Acc arg

   mutual recursion on Acc arg
   + need "sym_arg order" relation in which gamma < x :: gamma
 *)

Require Import Omega.
Program Fixpoint p9 (tbl : parse_table)
                    (sym : symbol)
                    (input : list string)
                    (vis : list nonterminal)
                    {measure (m9 tbl input vis) (pair_lt)}
  : (option tree * list string) :=
  match (sym, input) with
  | (T _, nil) => (None, input)
  | (T y, token :: input') =>
    if beqString y token then
      (Some (Leaf y), input')
    else
      (None, input)
  | (NT x, _) =>
    match pt_lookup x (peek input) tbl with
    | None => (None, input)
    | Some gamma =>
      if List.in_dec NT_as_DT.eq_dec x vis then
        (None, input)
      else
        let fix pf9 gamma pf_input pf_vis (H : pair_lt (m9 tbl pf_input pf_vis) (m9 tbl input vis)) :=
            match gamma with
            | nil => (Some nil, pf_input)
            | sym :: gamma' =>
              match p9 tbl sym pf_input pf_vis with
              | (None, _) => (None, input)
              | (Some lSib, lrem) =>
                match Compare_dec.lt_dec (List.length lrem) (List.length pf_input) with
                | left Hlt =>
                  match pf9 gamma' lrem [] _ with
                  | (None, _) => (None, lrem)
                  | (Some rSibs, rrem) =>
                    (Some (lSib :: rSibs), rrem)
                  end
                | right Hnlt =>
                  match pf9 gamma' pf_input pf_vis _ with
                  | (None, _) => (None, pf_input)
                  | (Some rSibs, rrem) =>
                    (Some (lSib :: rSibs), rrem)
                  end
                end
              end
            end
        in  match pf9 gamma input (x :: vis) _ with
            | (None, _) => (None, input)
            | (Some sts, input') =>
              (Some (Node x sts), input')
            end
    end
  end.
Next Obligation.
  apply pr_fst_lt.
  clear Heq_anonymous2.
  inv H.
  - omega.
  - omega.
Defined.
Next Obligation.
  unfold m9; simpl in *.
  apply pr_snd_lt.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec.
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
Defined.
Next Obligation.
  apply measure_wf.
  apply pair_lex_wf; apply lt_wf.
Defined.

Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (p9 tbl (NT X) ["a"] [])
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (p9 tbl
                                       (NT X)
                                       ["a"; "a"; "a"]
                                       [])
                end.

Eval compute in (p9 lr_table (NT X) ["a"] []).

Inductive sa_order : sym_arg -> sym_arg -> Prop := 
| f_lt_g : forall sym gamma,
    sa_order (F_arg sym) (G_arg gamma)
| g'_lt_g : forall gamma' gamma,
    List.length gamma' < List.length gamma
    -> sa_order (G_arg gamma') (G_arg gamma).

Definition m10 tbl (word : list string) (vis : list nonterminal) (sa : sym_arg) :=
  (List.length word,
   NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))                                     (fromNtList vis)),
   sa).

Definition lt10 : relation (nat * nat * sym_arg) :=
  triple_lex nat nat sym_arg lt lt sa_order.


(* working towards mutual recursion *)
Fixpoint p10 (tbl : parse_table)
             (sym : symbol)
             (input : list string)
             (vis : list nonterminal)
             (a : Acc lt10 (m10 tbl input vis (F_arg sym)))
             {struct a}
  : (option tree * list string).
  refine (match (sym, input) with
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
                let fix pf10 (tbl : parse_table)
                        (gamma : list symbol)
                        (input : list string)
                        (vis : list nonterminal)
                        (a : Acc lt10 (m10 tbl input vis (G_arg gamma)))
                        {struct a}
                    : (option (list tree) * list string) :=
                    match gamma as g return gamma = g -> _  with
                    | nil => fun _ => (Some nil, input)
                    | sym :: gamma' => fun Hg => 
                                         match p10 tbl sym input vis _ with
                                         | (None, _) => (None, input)
                                         | (Some lSib, input') =>
                                           match Compare_dec.lt_dec (List.length input') (List.length input) with
                                           | left Hlt =>
                                             match pf10 tbl gamma' input' [] _ with
                                             | (None, _) => (None, input)
                                             | (Some rSibs, input'') =>
                                               (Some (lSib :: rSibs), input'')
                                             end
                                           | right Hnlt =>
                                             match pf10 tbl gamma' input vis _ with
                                             | (None, _) => (None, input)
                                             | (Some rSibs, input'') =>
                                               (Some (lSib :: rSibs), input'')
                                             end
                                           end
                                         end
                    end eq_refl
              in  match pf10 tbl gamma input (x :: vis) _ with
                  | (None, _) => (None, input)
                  | (Some sts, input') =>
                    (Some (Node x sts), input')
                  end
              end
            end
          end).
  clear pf10.
  eapply Acc_inv; eauto.
  unfold m10; simpl.
  apply snd_lt.
  apply NP.subset_cardinal_lt with (x := x).
  - ND.fsetdec.
  - apply in_A_not_in_B_in_diff.
    + apply in_list_iff_in_fromNtList.
      eapply pt_lookup_in_nt_keys; eauto.
    + apply not_in_list_iff_not_in_fromNtList; auto.
  - ND.fsetdec.
    Unshelve.
    + eapply Acc_inv; eauto.
      * unfold m10.
        apply thd_lt.
        constructor.
    + eapply Acc_inv; eauto.
      apply fst_lt; auto.
    + eapply Acc_inv; eauto.
      apply thd_lt.
      constructor.
      subst.
      auto.
Defined.


Theorem sa_order_wf : well_founded sa_order.
Proof.
  unfold well_founded.
  intros a.
  induction a.
  - constructor; intros.
    inv H.
  - induction l.
    + constructor; intros.
      inv H.
      * constructor; intros.
        inv H.
      * inv H2.
    + constructor; intros.
      inv H.
      * constructor; intros.
        inv H.
      * destruct gamma'.
        -- constructor; intros.
           inv H.
           ++ constructor; intros.
              inv H.
           ++ inv H3.
        -- simpl in *.
           constructor; intros.
           inv H.
           ++ constructor; intros.
              inv H.
           ++ simpl in *.
              eapply Acc_inv; eauto.
              constructor.
              omega.
Defined.

Extraction p10.

Theorem lt10_wf : well_founded lt10.
  apply triple_lex_wf; try apply lt_wf.
  apply sa_order_wf.
Defined.

Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (p10 (lt10_wf (m10 tbl ["a"] [] (F_arg (NT X)))))
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (p10 (lt10_wf (m10 tbl ["a"; "a"; "a"] [] (F_arg (NT X)))))
                end.

Eval compute in (p10 (lt10_wf (m10 lr_table ["a"] [] (F_arg (NT X))))).

Lemma p11_hole1 :
  forall tbl input vis sa sa' x gamma,
    Acc lt10 (m10 tbl input vis sa)
    -> pt_lookup x (peek input) tbl = Some gamma
    -> ~ In x vis
    -> Acc lt10 (m10 tbl input (x :: vis) sa').
Proof.
  intros.
  eapply Acc_inv; eauto.
  unfold m10.
  apply snd_lt; simpl.
  apply NP.subset_cardinal_lt with (x := x); try ND.fsetdec.
  apply in_A_not_in_B_in_diff.
  - apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_nt_keys; eauto.
  - apply not_in_list_iff_not_in_fromNtList; auto.
Defined.

Lemma p11_hole2 :
  forall tbl input vis gamma sym,
    Acc lt10 (m10 tbl input vis (G_arg gamma))
    -> Acc lt10 (m10 tbl input vis (F_arg sym)).
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply thd_lt; constructor.
Defined.

Lemma p11_hole3 :
  forall tbl input input' vis vis' sa sa',
    Acc lt10 (m10 tbl input vis sa)
    -> List.length input' < List.length input
    -> Acc lt10 (m10 tbl input' vis' sa').
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply fst_lt; auto.
Defined.

Lemma p11_hole4 :
  forall tbl input vis gamma sym gamma',
    Acc lt10 (m10 tbl input vis (G_arg gamma))
    -> gamma = sym :: gamma'
    -> Acc lt10 (m10 tbl input vis (G_arg gamma')).
Proof.
  intros.
  eapply Acc_inv; eauto.
  apply thd_lt; subst.
  constructor; auto.
Defined.

Fixpoint p11 (tbl : parse_table)
             (sym : symbol)
             (input : list string)
             (vis : list nonterminal)
             (a : Acc lt10 (m10 tbl input vis (F_arg sym)))
             {struct a}
  : (option tree * list string).
  refine (match (sym, input) with
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
                let fix pf11 (tbl : parse_table)
                        (gamma : list symbol)
                        (input : list string)
                        (vis : list nonterminal)
                        (a : Acc lt10 (m10 tbl input vis (G_arg gamma)))
                        {struct a}
                    : (option (list tree) * list string) :=
                    match gamma as g return gamma = g -> _  with
                    | nil => fun _ => (Some nil, input)
                    | sym :: gamma' => fun Hg => 
                                         match p11 tbl sym input vis (p11_hole2 _ a) with
                                         | (None, _) => (None, input)
                                         | (Some lSib, input') =>
                                           match Compare_dec.lt_dec (List.length input') (List.length input) with
                                           | left Hlt =>
                                             match pf11 tbl gamma' input' [] (p11_hole3 _ _ _ a Hlt) with
                                             | (None, _) => (None, input)
                                             | (Some rSibs, input'') =>
                                               (Some (lSib :: rSibs), input'')
                                             end
                                           | right Hnlt =>
                                             match pf11 tbl gamma' input vis (p11_hole4 a Hg) with
                                             | (None, _) => (None, input)
                                             | (Some rSibs, input'') =>
                                               (Some (lSib :: rSibs), input'')
                                             end
                                           end
                                         end
                    end eq_refl
              in  match pf11 tbl gamma input (x :: vis) (p11_hole1 _ _ a Hlk Hnin) with
                  | (None, _) => (None, input)
                  | (Some sts, input') =>
                    (Some (Node x sts), input')
                  end
              end
            end
          end).
Defined.

Fixpoint p12 (tbl : parse_table)
             (sym : symbol)
             (input : list string)
             (vis : list nonterminal)
             (a : Acc lt10 (m10 tbl input vis (F_arg sym)))
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
    match pt_lookup x (peek input) tbl as o return pt_lookup x (peek input) tbl = o -> _ with
    | None => fun _ => (None, input)
    | Some gamma =>
      fun Hlk => match List.in_dec NT_as_DT.eq_dec x vis with
                 | left _ => (None, input)
                 | right Hnin => 
                   match pf12 (p11_hole1 (G_arg gamma) x a Hlk Hnin) with
                   | (None, _) => (None, input)
                   | (Some sts, input') =>
                     (Some (Node x sts), input')
                   end
                 end
    end eq_refl
  end
with pf12 (tbl : parse_table)
          (gamma : list symbol)
          (input : list string)
          (vis : list nonterminal)
          (a : Acc lt10 (m10 tbl input vis (G_arg gamma)))
          {struct a}
     : (option (list tree) * list string) :=
       match gamma as g return gamma = g -> _  with
       | nil => fun _ => (Some nil, input)
       | sym :: gamma' => fun Hg => 
                            match p12 (p11_hole2 sym a) with
                            | (None, _) => (None, input)
                            | (Some lSib, input') =>
                              match Compare_dec.lt_dec (List.length input') (List.length input) with
                              | left Hlt =>
                                match pf12 (p11_hole3 input' [] (G_arg gamma') a Hlt) with
                                | (None, _) => (None, input)
                                | (Some rSibs, input'') =>
                                  (Some (lSib :: rSibs), input'')
                                end
                              | right Hnlt =>
                                match pf12 (p11_hole4 a Hg) with
                                | (None, _) => (None, input)
                                | (Some rSibs, input'') =>
                                  (Some (lSib :: rSibs), input'')
                                end
                              end
                            end
       end eq_refl.

Extraction p12.

Eval compute in match parseTableOf yy_grammar with
                | None => None
                | Some tbl => Some (p12 (lt10_wf (m10 tbl ["a"] [] (F_arg (NT X)))))
                end.

Eval compute in match parseTableOf a_generator with
                | None => None
                | Some tbl => Some (p12 (lt10_wf (m10 tbl ["a"; "a"; "a"] [] (F_arg (NT X)))))
                end.

Eval compute in (p10 (lt10_wf (m10 lr_table ["a"] [] (F_arg (NT X))))).

(* next steps :

   - more expressive return type (partial parse tree, left-recursive nonterminal, etc.
   - condense two match expressions in parseForest into single expression? 
   - way to make arguments to recursive calls more syntactically obvious? 
   - soundness proof
   - remove previous drafts from code base
*)