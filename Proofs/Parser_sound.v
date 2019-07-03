Require Import List.
Require Import Omega.
Require Import String.
Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Require Import Parser.
Import ListNotations.

Module ParserSoundnessFn (Import G : Grammar.T).

  Module Export ParserDefs := ParserFn G.
  Module Import L := LemmasFn G.

  Ltac dms :=
    repeat match goal with
           | H : context[match ?X with _ => _ end] |- _ =>
             match X with
             | parseSymbol _ _ _ _ _ => idtac
             | parseGamma _ _ _ _ _ => idtac
             | _ => dm
             end
           | |- context[match ?X with _ => _ end] =>
             match X with
             | parseSymbol _ _ _ _ _ => idtac
             | parseGamma _ _ _ _ _ => idtac
             | _ => dm
             end
           end.

  Ltac dlle := match goal with
               | H : length_lt_eq _ _ _ |- _ => destruct H; subst
               end.
  
  Ltac induct_list_length xs := 
    remember (List.length xs) as l;
    generalize dependent xs;
    induction l as [l IHl] using lt_wf_ind;
    intros input Hl; subst.
  
  Ltac induct_card tbl vis :=
    remember (NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl))
                                         vis)) as card;
    generalize dependent vis;
    induction card as [card IHcard] using lt_wf_ind;
    intros vis Hcard; subst.
  
  Ltac induct_sa_size sa := 
    remember (sa_size sa) as sz;
    generalize dependent sa;
    induction sz as [sz IHsz] using lt_wf_ind;
    intros sa Hsa; subst.

  Lemma list_neq_cons :
    forall A (x : A) (xs : list A),
      xs <> x :: xs.
  Proof.
    unfold not; intros A x xs Heq; induction xs as [| x' xs IHxs]; try inv Heq; auto.
  Qed.
  
  Lemma parseSymbol_sound' :
    forall g tbl,
      parse_table_correct tbl g
      -> forall (ts    : list token)
                (vis   : NtSet.t)
                (sa    : sym_arg),
        match sa with
        | F_arg sym =>
          forall (a   : Acc triple_lt (meas tbl ts vis (F_arg sym)))
                 (v   : symbol_semty sym)
                 (r   : list token)
                 (Hle : length_lt_eq _ r ts),
            parseSymbol tbl sym ts vis a = inr (v, existT _ r Hle)
            -> exists word,
              word ++ r = ts
              /\ sym_derives_prefix g sym word v r
        | G_arg gamma =>
          forall (a   : Acc triple_lt (meas tbl ts vis (G_arg gamma)))
                 (vs  : rhs_semty gamma)
                 (r   : list token)
                 (Hle : length_lt_eq _ r ts),
            parseGamma tbl gamma ts vis a = inr (vs, existT _ r Hle)
            -> exists word,
              word ++ r = ts
              /\ gamma_derives_prefix g gamma word vs r
        end.
  Proof.
    intros g tbl Htbl ts.
    induct_list_length ts.
    intros vis; induct_card tbl vis.
    intros sa; induct_sa_size sa.
    destruct sa.
    - intros a v r Hle Hp; destruct a; simpl in *.
      dms; tc.
      + (* terminal *)
        invh. eexists; split; eauto.
        rewrite <- cons_app_singleton; auto.
      + (* nonterminal *)
        step_eq Hpf; dms; tc; invh.
        eapply IHcard with (sa := G_arg l) in Hpf; eauto.
        * destruct Hpf as [word [Happ Hg]]; subst.
          apply Htbl in e.
          destruct e as [Heq [Hin Hlk]]; simpl; eauto.
        * eapply cardinal_diff_add_lt; eauto.
    - intros a vs r Hle Hpf; destruct a; simpl in *; dms; tc.
      + invh.
        exists nil; eauto.
      + step_eq Hp; dms; tc; subst.
        * (* input length reduced *)
          step_eq Hpf'; dms; tc; invh.
          eapply IHsz with (m := sa_size (F_arg s)) (sa := F_arg s) in Hp;
            try (simpl; omega).
          eapply IHl with (sa := G_arg l) in Hpf'; eauto.
          destruct Hp as [wpre [Happ Hs]]; subst.
          destruct Hpf' as [wsuf [Happ Hg]]; subst.
          exists (wpre ++ wsuf); split; auto.
          rewrite <- app_assoc; auto.
        * (* input length unchanged *)
          step_eq Hpf'; dms; tc; invh.
          apply IHsz with (sa := F_arg s) (m := sa_size (F_arg s)) in Hp;
            try (simpl; omega).
          eapply IHsz with (sa := G_arg l) in Hpf'; eauto.
          destruct Hp as [wpre [Happ Hs]].
          apply l_ident_eq_nil in Happ; subst.
          destruct Hpf' as [wsuf [Happ Hg]]; subst.
          exists ([] ++ wsuf); split; auto.
  Qed.

  Lemma parseSymbol_sound :
    forall (g    : grammar)
           (tbl  : parse_table)
           (s    : symbol)
           (ts   : list token)
           (vis  : NtSet.t)
           (Hacc : Acc triple_lt (meas tbl ts vis (F_arg s)))
           (v    : symbol_semty s)
           (r    : list token)
           (Hle  : length_lt_eq _ r ts),
      parse_table_correct tbl g
      -> parseSymbol tbl s ts vis Hacc = inr (v, existT _ r Hle)
      -> exists w,  
          w ++ r = ts
          /\ sym_derives_prefix g s w v r.
  Proof.
    intros g tbl s ts r vis a v Hle Htbl Hp.
    eapply parseSymbol_sound' with (sa := F_arg s) in Hp; eauto.
  Qed.

End ParserSoundnessFn.

