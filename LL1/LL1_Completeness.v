Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof LL1.MonotonicityLemmas
        LL1.LL1_Derivation.
Open Scope string_scope.

Theorem parse_complete :
  forall (g : grammar)
         (tbl : parse_table),
    isParseTableFor tbl g
         -> forall (tr     : tree)
                   (sym    : symbol)
                   (wpre wsuf : list string),
      (@sym_derives_prefix g) sym wpre tr wsuf
      -> exists (fuel : nat),
          parse tbl sym (wpre ++ wsuf) fuel = (Some tr, wsuf).
Proof.
  intros g tbl Htbl tr sym wpre wsuf Hder.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction Hder using sdp_mutual_ind with
      
      (P := fun sym wpre tr wsuf
                (pf : sym_derives_prefix sym wpre tr wsuf) =>
              exists (fuel : nat),
                parse tbl sym (wpre ++ wsuf) fuel =
                (Some tr, wsuf))

      (P0 := fun gamma wpre f wsuf
             (pf : gamma_derives_prefix gamma wpre f wsuf) =>
               exists fuel,
                 parseForest tbl gamma (wpre ++ wsuf) fuel =
                 (Some f, wsuf)).

  - (* T case *)
    exists 1. simpl.
    destruct (Utils.beqString y y) eqn:Hbeq.
    + reflexivity.
    + unfold Utils.beqString in Hbeq. (*lemma*)
      destruct (StringMapFacts.eq_dec) in Hbeq.
      * inv Hbeq.
      * congruence. 

  - (* NTFirst case *)
    destruct IHHder as [fuel].
    exists (S fuel); simpl.
    destruct wpre as [| tok toks]; simpl in *.
    + inv f.
      eapply eof_fgamma in H3; eauto; inv H3. (*tactic*)
    + unfold ptComplete in Hcom.
      assert ((@isLookaheadFor g) (LA tok) (NT x) gamma).
      { unfold isLookaheadFor; auto. } (*lemma*)
      eapply Hcom in H0.
      destruct H0 as [m [Hs Hl]].
      unfold parseTableLookup; rewrite Hs; rewrite Hl. (*tac*)
      rewrite H.
      auto.

  - (* NtFollow case *)
    destruct IHHder as [fuel]; simpl in *.
    exists (S fuel); simpl.
    assert ((@isLookaheadFor g) (peek wsuf) (NT x) gamma).
    { unfold isLookaheadFor.
      right; split; auto.
      inv f.
      eapply gamma_derives_nil_nullable in g0; eauto.
      constructor; auto. } (*lemma*)
    apply Hcom in H0.
    destruct H0 as [m [Hs Hl]].
    unfold parseTableLookup; rewrite Hs; rewrite Hl.
    rewrite H.
    auto.

  - exists 1; simpl; auto.

  - destruct IHHder as [hdFuel].
    destruct IHHder0 as [tlFuel].
    eapply parse_fuel_max in H.
    eapply parseForest_fuel_max in H0.
    rewrite Max.max_comm in H0.
    exists (S (Nat.max hdFuel tlFuel)); simpl.
    rewrite <- app_assoc.
    rewrite H.
    rewrite H0.
    auto.
Qed.
