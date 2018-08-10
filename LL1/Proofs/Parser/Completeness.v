Require Import List.
Require Import String.

Require Import Lib.Grammar.
Require Import Lib.Lemmas.
Require Import Lib.ParseTree.
Require Import Lib.Tactics.
Require Import Lib.Utils.

Require Import LL1.Derivation.
Require Import LL1.Parser.
Require Import LL1.ParseTable.
Require Import LL1.Proofs.Parser.Monotonicity.

Theorem parse_complete :
  forall (g : grammar)
         (tbl : parse_table),
    parse_table_for tbl g
    -> forall (tr : tree)
              (sym : symbol)
              (word rem : list string),
      (@sym_derives_prefix g) sym word tr rem
      -> exists (fuel : nat),
        parse tbl sym (word ++ rem) fuel = (Some tr, rem).
Proof.
  intros g tbl Htbl tr sym word rem Hder.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction Hder using sdp_mutual_ind with
      
      (P := fun sym word tr rem (pf : sym_derives_prefix sym word tr rem) =>
              exists (fuel : nat),
                parse tbl sym (word ++ rem) fuel = (Some tr, rem))

      (P0 := fun gamma word f rem (pf : gamma_derives_prefix gamma word f rem) =>
               exists fuel,
                 parseForest tbl gamma (word ++ rem) fuel = (Some f, rem)).

  - (* T case *)
    exists 1; simpl.
    rewrite beqString_refl; auto.

  - (* NT case *)
    destruct IHHder as [fuel].
    exists (S fuel); simpl.
    apply Hcom in l.
    rewrite l.
    rewrite H; auto.

  - (* nil case *)
    exists 1; simpl; auto.

  - (* cons case *)
    destruct IHHder as [hdFuel].
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

