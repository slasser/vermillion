Require Import List.
Require Import Omega.
Require Import String.
Require Import Grammar.
Require Import Tactics.
Require Import Parser_safe.
Require Import Generator.
Require Import Lemmas.
Import ListNotations.

Module ParserProofsFn (Import G : Grammar.T).

  Module Export ParserSafety := ParserSafetyFn G.
  Module Import L := LemmasFn G.

  Theorem parseTree_complete_or_leftrec :
  forall g tbl sym word tr rem,
    parse_table_correct tbl g
    -> (@sym_derives_prefix g) sym word tr rem
    -> forall vis a,
        (exists x vis' input',
            parseTree tbl sym (word ++ rem) vis a = inl (LeftRec x vis' input'))
        \/ (exists Hle,
               parseTree tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle)).
Proof.
  intros g tbl sym word tr rem Htbl Hd.
  induction Hd using sdp_mutual_ind with
      (P := fun sym word tr rem (H : sym_derives_prefix sym word tr rem) =>
              forall vis a,
                (exists x vis' input',
                    parseTree tbl sym (word ++ rem) vis a = inl (LeftRec x vis' input'))
                \/ (exists Hle,
                       parseTree tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle)))
      
      (P0 := fun gamma word f rem (H : gamma_derives_prefix gamma word f rem) =>
               forall vis a,
                 (exists x vis' input',
                     parseForest_nf tbl gamma (word ++ rem) vis a = inl (LeftRec x vis' input'))
                 \/ (exists Hle,
                        parseForest_nf tbl gamma (word ++ rem) vis a = inr (f, existT _ rem Hle))); intros vis a.

  - right.
    eexists.
    destruct a.
    step; tc.

  - destruct a; step.
    + exfalso.
      apply Htbl in l; tc.
    + destruct s as [gamma' Hlk].
      assert (gamma' = gamma).
      { apply Htbl in l; auto.
        eapply lookups_eq; eauto. }
      subst.
      step; eauto.
      edestruct IHHd with (vis := NtSet.add x vis).
      * destruct H as [x' [vis' [input' Hpf]]].
        rewrite Hpf.
        left; eauto.
      * destruct H as [Hle Hpf].
        rewrite Hpf.
        right; eauto.

  - simpl in *.
    right.
    destruct a; simpl.
    eauto.

  - destruct a; simpl.
    rewrite app_assoc in IHHd.
    edestruct IHHd with (vis := vis).
    + destruct H as [x' [vis' [input' Hp]]].
      rewrite Hp; eauto.
    + destruct H as [Hp_le Hp].
      rewrite Hp.
      clear IHHd.
      step.
      * (* length lt case *)
        edestruct IHHd0.
        -- destruct H as [x [vis' [input' Hpf]]].
           rewrite Hpf; eauto.
        -- destruct H as [Hpf_le Hpf].
           rewrite Hpf; eauto.
      * assert (wpre = nil).
        { eapply l_ident_eq_nil with
              (xs := wpre) (ys := wsuf ++ rem).
          rewrite app_assoc; auto. }
        subst; simpl in *.
        edestruct IHHd0.
        -- destruct H as [x [vis' [input' Hpf]]].
           rewrite Hpf; eauto.
        -- destruct H as [Hpf_le Hpf].
           rewrite Hpf; eauto.
Qed.

Theorem parseTree_complete' :
  forall g tbl sym word tr rem,
    parse_table_correct tbl g
    -> (@sym_derives_prefix g) sym word tr rem
    -> exists Hle,
        parse_wrapper tbl sym (word ++ rem) = inr (tr, existT _ rem Hle).
Proof.
  intros.
  eapply parseTree_complete_or_leftrec in H0; eauto.
  destruct H0; eauto.
  exfalso.
  destruct H0 as [x [vis' [input' Hp]]].
  eapply parseTree_safe; eauto.
Qed.

End ParserProofsFn.

