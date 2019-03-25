Require Import List.
Require Import Omega.
Require Import String.
Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.
Require Import Lib.Utils.
Require Import LL1.Derivation.
Require Import LL1.Parser.
Require Import LL1.ParseTable.
Require Import LL1.ParseTableGen.
Import ListNotations.

Lemma parse_nf_eq_body :
  forall tbl sym input vis a,
    parse_nf tbl sym input vis a =
      match sym with
  | T a =>
    match input as i return input = i -> _ with
    | nil =>
      fun _ => inl (Reject "input exhausted" input)
    | token :: input' => 
      fun Hin => 
        if string_dec a token then
          inr (Leaf a, existT _ input' (length_lt_eq_cons _ _ _ _ Hin))
        else
          inl (Reject "token mismatch" input)
    end eq_refl
  | NT x =>
    match ptlk_dec x (peek input) tbl with
    | inl _ => inl (Reject "lookup failure" input)
    | inr (exist _ gamma Hlk) =>
      match mem_dec x vis with
      | left _ => inl (LeftRec x vis input)
      | right Hnin =>
        match parseForest_nf tbl gamma input (NtSet.add x vis) (hole1 _ _ _ _ _ _ _ a Hlk Hnin) with
        | inl pfail => inl pfail
        | inr (sts, existT _ input' Hle) =>
          inr (Node x sts, existT _ input' Hle)
        end
      end
    end
  end.
Proof.
  intros; simpl; destruct a; cr.
Qed.

Lemma parseForest_nf_eq_body :
  forall tbl gamma input vis a,
    parseForest_nf tbl gamma input vis a =
        match gamma as g return gamma = g -> _  with
    | nil => fun _ => inr (nil, existT (fun input' => length_lt_eq string input' input) input
                                       (length_lt_eq_refl _ _))
    | sym :: gamma' => fun Hg => 
                         match parse_nf tbl sym input vis (hole2 _ _ _ _ _ a) with
                         | inl pfail => inl pfail
                         | inr (lSib, existT _ input' Hle) =>
                           match Hle with
                           | left Hlt =>
                             match parseForest_nf tbl gamma' input' NtSet.empty (hole3 _ _ _ _ _ _ _ a Hlt) with
                             | inl pfail => inl pfail
                             | inr (rSibs, existT _ input'' Hle'') =>
                               inr (lSib :: rSibs, existT _ input'' (length_lt_eq_trans _ _ _ _ Hle'' Hle))
                             end
                           | right Heq =>
                             match parseForest_nf tbl gamma' input vis (hole4 _ _ _ _ _ _ a Hg) with
                             | inl pfail => inl pfail
                             | inr (rSibs, existT _ input'' Hle'') =>
                               inr (lSib :: rSibs, existT _ input'' Hle'')
                             end
                           end
                         end
    end eq_refl.
Proof.
  intros; simpl; destruct a; cr.
Qed.

Lemma parse_t_ret_leaf :
  forall tbl
         input rem
         vis
         y
         (a : Acc triple_lt (meas tbl input vis (F_arg (T y))))
         tr,
    parse_nf tbl (T y) input vis a = inr (tr, rem)
    -> isLeaf tr = true.
Proof.
  intros; destruct a; cr; tc.
  inv H; auto.
Qed.

Lemma parse_nt_ret_node :
  forall tbl
         input rem
         vis
         x
         (a : Acc triple_lt (meas tbl input vis (F_arg (NT x))))
         tr,
    parse_nf tbl (NT x) input vis a = inr (tr, rem)
    -> isNode tr = true.
Proof.
  intros; destruct a; cr; tc.
  inv H; auto.
Qed.

Lemma lengths_contra :
  forall A (xs ys : list A),
    List.length xs = List.length ys
    -> List.length xs < List.length ys
    -> False.
Proof.
  intros; omega.
Qed.

Lemma input_length_invariant :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              Hle
              (vis       : NtSet.t)
              (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
      parse_nf tbl sym input vis a = inr (tr, existT _ rem Hle)
      -> List.length rem < List.length input
         \/ nullable_sym g sym.
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
                     Hle
                     (vis : NtSet.t)
                     (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                parseForest_nf tbl gamma input vis a = inr (f, existT _ rem Hle)
                -> List.length rem < List.length input
                   \/ nullable_gamma g gamma); intros; destruct a.

  - destruct sym as [y | x].
    + cr; tc.
      inv H; auto.
    + apply parse_nt_ret_node in H; inv H.

  - destruct sym as [y | x].
    + apply parse_t_ret_leaf in H; inv H.
    + step; tc.
      step.
      step; tc.
      step_eq Hpf; tc.
      step.
      step.
      inv H.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf; auto.
      right.
      apply Htbl in e; destruct e.
      econstructor; eauto.

  - cr; tc.

  - step; tc.
    step_eq Hp; tc.
    step.
    step.
    step.
    + left.
      step_eq Hpf; tc.
      step.
      step.
      inv H.
      destruct l1; subst; omega.
    + subst.
      step_eq Hpf; tc.
      step.
      step.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp; try omega.
      destruct Hpf; auto.
Qed.

Lemma parse_sound' :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (input rem : list terminal)
              Hle
              (vis       : NtSet.t)
              (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
      parse_nf tbl sym input vis a = inr (tr, existT _ rem Hle)
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
                     Hle
                     (vis : NtSet.t)
                     (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                parseForest_nf tbl gamma input vis a = inr (f, existT _ rem Hle)
                -> exists word,
                  word ++ rem = input
                  /\ gamma_derives_prefix gamma word f rem); intros; destruct a.

  - destruct sym as [y | x].
    + rewrite parse_nf_eq_body in H.
      step; tc.
      step_eq Hbeq; tc.
      inv H.
      eexists; split.
      * rewrite cons_app_singleton; auto.
      * constructor; auto.
    + apply parse_nt_ret_node in H; inv H.

  - destruct sym as [y | x].
    + apply parse_t_ret_leaf in H; inv H.
    + simpl in H.
      destruct (ptlk_dec x (peek input) tbl) as [| e]; tc.
      destruct e as [gamma Hlk].
      step; tc.
      step_eq Hpf; tc.
      step.
      step.
      inv H.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf as [word [Happ Hg]]; subst.
      eexists; split; eauto.
      apply Htbl in Hlk; destruct Hlk.
      econstructor; eauto.

  - rewrite parseForest_nf_eq_body in H.
    cr; tc.
    inv H.
    exists nil; split; auto.
    constructor.

  - rewrite parseForest_nf_eq_body in H.
    step; tc.
    step_eq Hp; tc.
    step.
    step.
    step.
    + (* length_lt case *)
      step_eq Hpf; tc.
      step; tc.
      step.
      inv H.
      apply IHp in Hp; clear IHp.
      apply IHpf in Hpf; clear IHpf.
      destruct Hp  as [wpre [Happ Hs]]; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists (wpre ++ wsuf); split.
      * rewrite app_assoc; auto.
      * constructor; auto.
    + subst.
      step_eq Hpf; tc.
      step.
      step.
      inv H.
      eapply IHp in Hp; clear IHp.
      eapply IHpf in Hpf; clear IHpf.
      destruct Hp as [wpre [Happ Hs]].
      apply l_ident_eq_nil in Happ; subst.
      destruct Hpf as [wsuf [Happ Hg]]; subst.
      exists ([] ++ wsuf); split; auto.
      constructor; auto.
Qed.

Lemma parse_sound :
  forall (g   : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr        : tree)
              (sym       : symbol)
              (word rem  : list terminal)
              Hle
              (vis       : NtSet.t)
              (a : Acc triple_lt (meas tbl (word ++ rem) vis (F_arg sym))),
      parse_nf tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle)
      -> (@sym_derives_prefix g) sym word tr rem.
Proof.
  intros g tbl Htbl tr sym word rem Hle vis a Hp.
  pose proof Hp as Hp'.
  eapply parse_sound' in Hp; eauto.
  destruct Hp as [word' [Happ Hder]].
  apply app_inv_tail in Happ.
  subst; auto.
Qed.

