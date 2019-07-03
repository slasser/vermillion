Require Import List.
Require Import Omega.
Require Import String.
Require Import Grammar.
Require Import Tactics.
Require Import Parser_safe.
Require Import Lemmas.
Import ListNotations.

Module ParserProofsFn (Import G : Grammar.T).
  
  Module Export ParserSafety := ParserSafetyFn G.
  Module Import L := LemmasFn G.

  Lemma eq_rect_terminal_eq :
    forall (a   : terminal)
           (v   : t_semty a)
           (Heq : a = a),
      eq_rect a t_semty v a Heq = v.
  Proof.
    intros a v Heq.
    erewrite Eqdep_dec.eq_rect_eq_dec; eauto.
  Qed.

  Lemma eq_rect_nonterminal_eq :
    forall (x   : nonterminal)
           (v   : nt_semty x)
           (Heq : x = x),
      eq_rect x nt_semty v x Heq = v.
  Proof.
    intros x v Heq.
    erewrite Eqdep_dec.eq_rect_eq_dec; eauto.
  Qed.
  
  Theorem parseSymbol_complete_or_error :
    forall (g : grammar)
           (tbl : parse_table)
           (s : symbol)
           (w r : list token)
           (v : symbol_semty s),
      parse_table_correct tbl g
      -> sym_derives_prefix g s w v r
      -> forall vis a,
          (exists m x ts',
              parseSymbol tbl s (w ++ r) vis a = inl (Error m x ts'))
          \/ (exists Hle,
                 parseSymbol tbl s (w ++ r) vis a = inr (v, existT _ r Hle)).
  Proof.
    intros g tbl s w v r Htbl Hd.
    induction Hd using sdp_mutual_ind with
        (P := fun s w v r (H : sym_derives_prefix g s w v r) =>
                forall vis a,
                  (exists m x ts',
                      parseSymbol tbl s (w ++ r) vis a = inl (Error m x ts'))
                  \/ (exists Hle,
                         parseSymbol tbl s (w ++ r) vis a = inr (v, existT _ r Hle)))
        
        (P0 := fun gamma w vs r (H : gamma_derives_prefix g gamma w vs r) =>
                 forall vis a,
                   (exists m x ts',
                       parseGamma tbl gamma (w ++ r) vis a = inl (Error m x ts'))
                   \/ (exists Hle,
                          parseGamma tbl gamma (w ++ r) vis a = inr (vs, existT _ r Hle))); intros vis a'.
    - right; eexists.
      destruct a'; simpl in *; dm; tc.
      rewrite eq_rect_terminal_eq; auto.
    - destruct a'; simpl in *; dm; tc; eauto.
      eapply Htbl in l; tc; eauto.
      destruct (ptlk_dec x (peek (w ++ r))) as
          [Hlk | [[(x', gamma') f'] Hlk]]; tc.
      rewrite Hlk in l; inv l.
      assert (f' = f).
      { apply Eqdep_dec.inj_pair2_eq_dec; auto.
        apply production_eq_dec. }
        subst; dms; tc.
        edestruct IHHd with (vis := NtSet.add x vis).
        * destruct H as [m [x' [ts' Hpf]]].
          rewrite Hpf; left; eauto.
        * destruct H as [Hle Hpf].
          rewrite Hpf; right.
          rewrite eq_rect_nonterminal_eq; eauto.
    - simpl in *.
      right.
      destruct a'; simpl; eauto.
    - destruct a'; simpl.
      rewrite app_assoc in IHHd.
      edestruct IHHd with (vis := vis); clear IHHd.
      + destruct H as [m [x [ts' Hp]]].
        rewrite Hp; eauto.
      + destruct H as [Hp_le Hp].
        rewrite Hp; dm.
        * (* length lt case *)
          edestruct IHHd0.
          -- destruct H as [m [x [ts' Hpf]]].
             rewrite Hpf; eauto.
          -- destruct H as [Hpf_le Hpf].
             rewrite Hpf; eauto.
        * assert (wpre = nil).
          { eapply l_ident_eq_nil with
                (xs := wpre) (ys := wsuf ++ r).
            rewrite app_assoc; auto. }
          subst; simpl in *.
          edestruct IHHd0.
          -- destruct H as [m [x [ts' Hpf]]].
             rewrite Hpf; eauto.
          -- destruct H as [Hpf_le Hpf].
             rewrite Hpf; eauto.
  Qed.
  
End ParserProofsFn.

