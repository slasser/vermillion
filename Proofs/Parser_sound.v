Require Import List.
Require Import Omega.
Require Import String.
Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Require Import Parser.
Require Import Generator.
Import ListNotations.

Module ParserSoundnessFn (Import G : Grammar.T).

  Module Export ParserDefs := ParserFn G.
  Module Import L := LemmasFn G.

  Ltac dms :=
    repeat match goal with
           | H : context[match ?X with _ => _ end] |- _ =>
             match X with
             | parseTree _ _ _ _ _ => idtac
             | parseForest _ _ _ _ _ => idtac
             | _ => dm
             end
           | |- context[match ?X with _ => _ end] =>
             match X with
             | parseTree _ _ _ _ _ => idtac
             | parseForest _ _ _ _ _ => idtac
             | _ => dm
             end
           end.

  Ltac dlle := match goal with
               | H : length_lt_eq _ _ _ |- _ => destruct H; subst
               end.
  (*
  Lemma lengths_contra :
    forall A (xs ys : list A),
      List.length xs = List.length ys
      -> List.length xs < List.length ys
      -> False.
  Proof.
    intros; omega.
  Qed.
   *)
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
  
  Lemma input_length_invariant :
    forall (g   : grammar)
           (tbl : parse_table),
      parse_table_correct tbl g
      -> forall (tr        : tree)
                (sym       : symbol)
                (input rem : list terminal)
                Hle
                (vis       : NtSet.t)
                (a : Acc triple_lt (meas tbl input vis (F_arg sym))),
        parseTree tbl sym input vis a = inr (tr, existT _ rem Hle)
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
                       (input rem : list terminal)
                       Hle
                       (vis : NtSet.t)
                       (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                  parseForest tbl gamma input vis a = inr (f, existT _ rem Hle)
                  -> List.length rem < List.length input
                     \/ nullable_gamma g gamma); intros; destruct a; simpl in *.

    - dms; tc.
      + invhs; auto. 
      + dm; dms; tc.

    - dms; tc.
      step_eq Hpf; dms; tc.
      invh.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf; auto.
      apply Htbl in e; destruct e; eauto.

    - dms.
      + invhs; auto.
      + dm; tc.
        dms; dm; dms; tc.

    - dms; tc.
      step_eq Hp; dms; tc.
      + step_eq Hpf; dms; tc.
        invh.
        dlle; auto.
        left; omega.
      + step_eq Hpf; dms; tc.
        invh.
        apply IHp in Hp; clear IHp.
        apply IHpf in Hpf; clear IHpf.
        destruct Hp; try omega.
        destruct Hpf; auto.
  Qed.
  
  Lemma parseTree_sound' :
    forall g tbl,
      parse_table_correct tbl g
      -> forall (input : list terminal)
                (vis   : NtSet.t)
                (sa    : sym_arg),
        match sa with
        | F_arg sym =>
          forall a tr rem Hle,
            parseTree tbl sym input vis a = inr (tr, existT _ rem Hle)
            -> exists word,
              word ++ rem = input
              /\ sym_derives_prefix g sym word tr rem
        | G_arg gamma =>
          forall a f rem Hle,
            parseForest tbl gamma input vis a = inr (f, existT _ rem Hle)
            -> exists word,
              word ++ rem = input
              /\ gamma_derives_prefix g gamma word f rem
        end.
  Proof.
    intros g tbl Htbl input.
    induct_list_length input.
    intros vis; induct_card tbl vis.
    intros sa; induct_sa_size sa.
    destruct sa.
    - intros a tr rem Hle Hp; destruct a; simpl in *.
      dms; tc.
      + (* terminal *)
        invh. eexists; split; eauto.
        rewrite <- cons_app_singleton; auto.
      + (* nonterminal *)
        step_eq Hpf; dms; tc; invh.
        eapply IHcard with (sa := G_arg x) in Hpf; eauto.
        * destruct Hpf as [word [Happ Hg]]; subst.
          apply Htbl in e; destruct e; eauto.
        * eapply cardinal_diff_add_lt; eauto.
    - intros a f rem Hle Hpf; destruct a; simpl in *; dms; tc.
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

  Lemma parseTree_sound :
    forall (g   : grammar)
           (tbl : parse_table),
      parse_table_correct tbl g
      -> forall (tr        : tree)
                (sym       : symbol)
                (word rem  : list terminal)
                Hle
                (vis       : NtSet.t)
                (a : Acc triple_lt (meas tbl (word ++ rem) vis (F_arg sym))),
        parseTree tbl sym (word ++ rem) vis a = inr (tr, existT _ rem Hle)
        -> sym_derives_prefix g sym word tr rem.
  Proof.
    intros g tbl Htbl tr sym word rem Hle vis a Hp.
    pose proof Hp as Hp'.
    eapply parseTree_sound' with (sa := F_arg sym) in Hp; eauto.
    destruct Hp as [word' [Happ Hder]].
    apply app_inv_tail in Happ.
    subst; auto.
  Qed.

End ParserSoundnessFn.

