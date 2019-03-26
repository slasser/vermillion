Require Import List.
Require Import Omega.
Require Import String.
Require Import Wf_nat.
Require Import Grammar.
Require Import ParseTree.
Require Import Tactics.
Require Import Proofs.Lemmas.
Require Import Parser.
Require Import ParseTable.
Require Import ParseTableGen.
Require Import Parser.
Require Import Derivation.
Require Import Completeness.
Require Import Soundness.
Import ListNotations.
Open Scope list_scope.

Definition sa_size (sa : sym_arg) : nat :=
  match sa with
  | F_arg _ => 0
  | G_arg gamma => 1 + List.length gamma
  end.

Lemma leftrec_conditions :
  forall g tbl,
    parse_table_for tbl g
    -> forall (input : list string)
              (vis : NtSet.t)
              (sa : sym_arg),
      match sa with
      | F_arg sym =>
        forall a x vis' input',
          parse_nf tbl sym input vis a = inl (LeftRec x vis' input')
          -> (NtSet.In x vis
              /\ (sym = NT x
                  \/ nullable_path g (peek input) sym (NT x)))
             \/ exists la, (left_recursive g (NT x) la)
      | G_arg gamma =>
        forall a x vis' input',
          parseForest_nf tbl gamma input vis a = inl (LeftRec x vis' input')
          -> (exists pre sym suf,
                 gamma = pre ++ sym :: suf
                 /\ nullable_gamma g pre
                 /\ NtSet.In x vis
                 /\ (sym = NT x
                     \/ nullable_path g (peek input) sym (NT x)))
             \/ exists la, (left_recursive g (NT x) la)
      end.
Proof.
  intros g tbl Ht input.

  remember (List.length input) as l.
  generalize dependent input.
  induction l as [l IHl] using lt_wf_ind.
  intros input Hl; subst.

  intros vis.
  remember (NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl)) vis)) as card.
  generalize dependent vis.
  induction card as [card IHcard] using lt_wf_ind.
  intros vis Hcard; subst.

  intros sa.
  remember (sa_size sa) as sz.
  generalize dependent sa.
  induction sz as [sz IHsz] using lt_wf_ind.
  intros sa Hsa; subst.
  destruct sa.

  - (* sa = F_arg sym *)
    intros a x vis' input' Hp; destruct a.
    step.
    + step; tc.
      step; tc.
    + step; tc.
      destruct s as [gamma Hlk].
      step.
      * (* x is in vis *)
        inv Hp.
        left; split; auto.
      *  (* x is not in vis *)
        step_eq Hpf.
        -- inv Hp.
           eapply IHcard with (sa := G_arg gamma) in Hpf; eauto.
           clear IHl; clear IHsz; clear IHcard.
           destruct Hpf as [Hex | Hex].
           ++ destruct Hex as [pre [sym [suf [Hg [Hng [Hin Hrest]]]]]]; subst.
              rename x into x'; rename n into x.
              destruct Hrest as [Hin' | Hnin].
              ** subst.
                 destruct (NtSetFacts.eq_dec x x').
                 --- subst.
                     right.
                     exists (peek input).
                     red.
                     apply Ht in Hlk.
                     destruct Hlk.
                     eapply DirectPath with (pre := pre); eauto.
                 --- left.
                     split.
                     +++ ND.fsetdec.
                     +++ right.
                         apply Ht in Hlk.
                         destruct Hlk.
                         eapply DirectPath; eauto.
              ** destruct (NtSetFacts.eq_dec x x').
                 --- subst.
                     right.
                     exists (peek input).
                     red.
                     destruct sym as [y | z].
                     +++ inv Hnin.
                     +++ apply Ht in Hlk; destruct Hlk.
                         eapply IndirectPath with (y := z); eauto.
                 --- left.
                     split.
                     +++ ND.fsetdec.
                     +++ right.
                         destruct sym.
                         *** inv Hnin.
                         *** apply Ht in Hlk; destruct Hlk.
                             eapply IndirectPath with (y := n1); eauto.
           ++ right; auto.
           ++ apply NP.subset_cardinal_lt with (x := n); try ND.fsetdec.
              apply in_A_not_in_B_in_diff; auto.
              apply in_list_iff_in_fromNtList.
              eapply pt_lookup_in_nt_keys; eauto.
        -- step.
           step; tc.

  - intros a x vis' input' Hpf; destruct a.
    step; tc.
    step_eq Hpf.
    + (* calling parse on s returns LeftRec *)
      inv Hpf.
      eapply IHsz with (sa := F_arg s) (m := sa_size (F_arg s)) in Hpf0; eauto.
      * destruct Hpf0; auto.
        left.
        exists nil; exists s; exists l; split; auto. 
      * simpl; omega.
    + (* calling parse on s succeeds, calling parseForest on l returns LeftRec *)
      step.
      step.
      step.
      * (* parse consumed some input *)
        step_eq Hpf.
        -- inv Hpf.
           eapply IHl with (sa := G_arg l) in Hpf1; eauto.
           destruct Hpf1.
           ++ destruct H as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]].
              ND.fsetdec.
           ++ right; auto. 
        -- step.
           step; tc.
      * (* parse consumed no input *)
        subst.
        step_eq Hpf.
        inv Hpf.
        eapply IHsz with (sa := G_arg l) in Hpf1; eauto.
        destruct Hpf1.
        -- destruct H as [pre [sym [suf [Heq [Hng [Hin Hrest]]]]]]; subst.
           left.
           exists (s :: pre); exists sym; exists suf.
           repeat split; auto.
           eapply input_length_invariant in Hpf0; eauto.
           destruct Hpf0; try omega.
           econstructor; eauto.
        -- right; auto.
        -- step.
           step; tc.
Qed.

Theorem parse_nf_safe :
  forall g tbl sym input x vis' input',
    parse_table_for tbl g
    -> ~ parse_wrapper tbl sym input = inl (LeftRec x vis' input').
Proof.
  intros g tbl sym input s vis' input' Htbl; unfold not; unfold parse_wrapper; intros Hp.
  eapply leftrec_conditions with (sa := F_arg sym) in Hp; eauto.
  destruct Hp.
  - ND.fsetdec.
  - destruct H as [la Hlr].
    eapply LL1_parse_table_impl_no_left_recursion; eauto.
Qed.

