Require Import Derivation.
Require Import Grammar.
Require Import List.
Require Import Parser.
Require Import ParserTactics.
Require Import ParseTable.
Require Import String.
Require Import Omega.
Import ListNotations.
Open Scope string_scope.

Lemma epsilon_step :
  forall (pt : parse_table)
         (stack : list symbol)
         (input : list string)
         (fuel : nat),
    parseLoop pt stack input fuel = true <->
    parseLoop pt (EPS :: stack) input (S fuel) = true.
Proof.
  split.
  - intros. simpl. assumption.
  - intros. simpl in H. assumption.
Defined.


Lemma terminal_step :
  forall (pt : parse_table)
         (tName : string)
         (token : string)
         (stack : list symbol)
         (input : list string)
         (fuel  : nat),
    cmpSymbol (T tName) (T token) = true ->
    parseLoop pt stack input fuel = true <->
    parseLoop pt (T tName :: stack) (token :: input) (S fuel) = true.
Proof.
  split.
  - intros. simpl. rewrite H. assumption.
  - intros. simpl in H0. rewrite H in H0. assumption.
Defined.


Lemma nonterminal_step :
  forall (pt : parse_table)
         (ntName : string)
         (token  : string)
         (x      : symbol)
         (ys     : list symbol)
         (stack  : list symbol)
         (input  : list string)
         (fuel   : nat),
    parseTableLookup (NT ntName) (T token) pt = Some (x, ys) ->
    parseLoop pt (ys ++ stack) (token :: input) fuel = true <->
    parseLoop pt (NT ntName :: stack) (token :: input) (S fuel) = true.
Proof.
  split.
  - intros. simpl. rewrite H. apply H0.
  - intros. simpl in H0. rewrite H in H0. apply H0.
Defined.

Lemma derives_singleton_list_of_NT_implies_derives_NT :
  forall (g : grammar)
         (ntName : string)
         (tokens : list string),
    (@derivesList2 g) [NT ntName] tokens ->
    (@derives2 g) (NT ntName) tokens.
Proof.
  intros. inv H. inv H4.
  rewrite app_nil_r. assumption.
Defined.


Theorem n_fuel_enough_implies_m_fuel_enough :
  forall (pt : parse_table)
         (stack : list symbol)
         (tokens : list string)
         (n m : nat),
    parseLoop pt stack tokens n = true ->  n < m ->
    parseLoop pt stack tokens m = true.
Proof.
  intros.
  generalize dependent m.
  generalize dependent tokens.
  generalize dependent stack.
  induction n.
  - intros. inv H.
  - intros. destruct m.
    + inv H0.
    + destruct stack.
      * reflexivity.
      * destruct s.
        (* epsilon case *)
        { rewrite <- epsilon_step in *.
          apply IHn.
          { assumption. }
          { omega. }}
        (* terminal case *)
        { destruct tokens.
          { inv H. }
          { simpl in H.
            destruct (cmpSymbol (T s) (T s0)) eqn:Hcmp.
            { rewrite <- terminal_step.
              { apply IHn.
                { assumption. }
                { omega. }}
              { assumption. }}
            { inv H. }}}
        (* nonterminal case *)
        { destruct tokens.
          { inv H. }
          { simpl in H.
            destruct (parseTableLookup (NT s) (T s0) pt) eqn:Hpt.
            { destruct p.
              rewrite <- nonterminal_step.
              { apply IHn.
                { apply H. }
                { omega. }}
              { apply Hpt. }}
            { inv H. }}}
Defined.


Lemma fuel_enough_implies_S_fuel_enough :
  forall (pt : parse_table)
         (stack : list symbol)
         (input : list string)
         (fuel : nat),
    parseLoop pt stack input fuel = true ->
    parseLoop pt stack input (S fuel) = true.
Proof.
  intros.
  apply n_fuel_enough_implies_m_fuel_enough
    with (n := fuel) (m := S fuel).
  - assumption.
  - omega.
Defined.


(* Proofs below are still in progress *)


Lemma parse_true_implies_derivesList :
  forall (g : grammar)
         (pt : parse_table)
         (stack : list symbol)
         (input : list string)
         (fuel : nat),
    parseLoop pt stack input fuel = true ->
    exists (prefix suffix : list string),
      (prefix ++ suffix)%list = input /\
      (@derivesList2 g) stack prefix.
Proof.
  intros. destruct fuel.
  - inv H.
  - induction stack.
    + exists nil, input. split.
      * reflexivity.
      * apply derivesNil2.
    + destruct a eqn:Hsym.
      * simpl in H. exists nil, input. split.
        { reflexivity. }
        { apply derivesCons2
            with (hdRoot := EPS) (prefix := []).
          { apply derivesEPS2. }
Abort.


Theorem parseLoop_correct :
  forall (g : grammar)
         (startSym : symbol)
         (input : list string)
         (fuel : nat),
    parseLoop (mkParseTable g fuel) [startSym] input fuel =
    true ->
    exists (prefix suffix : list string),
      (prefix ++ suffix)%list = input /\
      (@derives2 g) startSym prefix.
Proof.
  intros.
  destruct fuel.
  - inv H.
  - destruct startSym.
    (* epsilon case *)
    + exists nil, input. simpl. split.
      * reflexivity.
      * apply derivesEPS2.
    (* terminal case *)    
    + destruct input.
      * inv H.
      * exists [s0], input. simpl. split.
        { reflexivity. }
        { assert (s = s0).
          { unfold parseLoop in H.
            unfold cmpSymbol in H.
            destruct (SymbolAsDT.eq_dec (T s) (T s0)).
Abort.