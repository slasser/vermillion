Require Import List.
Require Import String.

Require Import Lib.Grammar.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.
Require Import Lib.Utils.

Require Import LL1.Derivation.
Require Import LL1.Lemmas.
Require Import LL1.Parser.
Require Import LL1.ParseTable.

Lemma LL1_derivation_deterministic :
  forall (tbl : parse_table)
         (g : grammar),
    parse_table_for tbl g
    -> forall (sym : symbol)
              (word rem : list string)
              (tr : tree),
      (@sym_derives_prefix g) sym word tr rem
      -> forall (word' rem' : list string)
                (tr' : tree),
        (@sym_derives_prefix g) sym word' tr' rem'
        -> word ++ rem = word' ++ rem'
        -> word = word' /\ rem = rem' /\ tr = tr'.
Proof.
  intros tbl g Htbl sym word rem tr Hder.
  induction Hder using sdp_mutual_ind with
      
      (P := fun sym word tr rem (pf : sym_derives_prefix sym word tr rem) =>
              forall word' rem' tr',
                sym_derives_prefix sym word' tr' rem'
                -> word ++ rem = word' ++ rem'
                -> word = word' /\ rem = rem' /\ tr = tr')
      
      (P0 := fun gamma word f rem (pf : gamma_derives_prefix gamma word f rem) =>
               forall word' rem' f',
                 gamma_derives_prefix gamma word' f' rem'
                 -> word ++ rem = word' ++ rem'              
                 -> word = word' /\ rem = rem' /\ f = f').
  
  - (* T case *)
    intros word' rem' tr' Hsdp Happ.
    inv Hsdp; inv Happ; auto.
    
  - (* NT case *)
    intros word' rem' tr' Hsdp Happ.
    inv Hsdp.
    (* The two right-hand sides must be equal because the grammar is LL(1) *)
    assert (gamma0 = gamma).
    { destruct l as [Hin Hlk].
      destruct H0 as [Hin' Hlk'].
      destruct Hlk as [Hfi | Hfo]; destruct Hlk' as [Hfi' | Hfo'].
      - (* first-first case *)
        rewrite <- Happ in Hfi'.
        destruct Htbl as [Hmin Hcom].
        assert (lookahead_for (peek (word ++ rem)) x gamma g) by (split; auto).
        assert (lookahead_for (peek (word ++ rem)) x gamma0 g) by (split; auto).
        apply Hcom in H.
        apply Hcom in H0.
        destruct H as [m [Hs Hl]].
        destruct H0 as [m' [Hs' Hl']].
        congruence.
      - (* first-follow conflict *)
        exfalso.
        destruct Hfo'.
        eapply no_first_follow_conflicts with (sym := NT x); eauto.
        rewrite <- Happ.
        eapply first_gamma_first_sym with
            (la := peek (word ++ rem))
            (gamma := gamma); eauto.
      - (* first-follow conflict *)
        exfalso.
        destruct Hfo.
        eapply no_first_follow_conflicts with (sym := NT x); eauto.
        rewrite Happ.
        eapply first_gamma_first_sym; eauto.
      - (* follow-follow case *)
        destruct Hfo as [Hnu Hfo]; destruct Hfo' as [Hnu' Hfo'].
        destruct Htbl as [Hmin Hcom].
        unfold pt_complete in Hcom.
        rewrite <- Happ in Hfo'.
        assert (Hlk : lookahead_for (peek (word ++ rem)) x gamma g)
          by (split; auto).
        assert (Hlk' : lookahead_for (peek (word ++ rem)) x gamma0 g)
          by (split; auto).
        apply Hcom in Hlk.
        apply Hcom in Hlk'.
        destruct Hlk as [m [Hs Hl]].
        destruct Hlk' as [m' [Hs' Hl']].
        congruence. }
    subst.
    eapply IHHder in H1; eauto.
    do 2 destruct H1; subst; auto.

  - (* nil case *)
    intros word' rem' f' Hgdp Happ.
    inv Hgdp; auto.

  - (* cons case *)
    intros word' rem' f' Hgdp Happ.
    inv Hgdp.
    eapply IHHder in H1; eauto.
    + destruct H1.
      destruct H0; subst.
      eapply IHHder0 in H5; eauto.
      destruct H5.
      destruct H1.
      subst; auto.
    + repeat rewrite app_assoc; auto.
Qed.

