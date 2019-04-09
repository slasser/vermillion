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

  Lemma parse_nf_eq_body :
    forall tbl sym input vis a,
      parseTree tbl sym input vis a =
      match sym with
      | T a =>
        match input as i return input = i -> _ with
        | nil =>
          fun _ => inl (Reject "input exhausted" input)
        | token :: input' => 
          fun Hin => 
            if t_eq_dec a token then
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
            match parseForest tbl gamma input (NtSet.add x vis)
                              (hole1 _ _ _ _ _ _ _ a Hlk Hnin)
            with
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

  Lemma parseForest_eq_body :
    forall tbl gamma input vis a,
      parseForest tbl gamma input vis a =
      match gamma as g return gamma = g -> _  with
      | nil => fun _ => inr (nil, existT (fun input' => length_lt_eq terminal input' input)
                                         input
                                         (length_lt_eq_refl _ _))
      | sym :: gamma' => fun Hg => 
                           match parseTree tbl sym input vis (hole2 _ _ _ _ _ a) with
                           | inl pfail => inl pfail
                           | inr (lSib, existT _ input' Hle) =>
                             match Hle with
                             | left Hlt =>
                               match parseForest tbl gamma' input' NtSet.empty
                                                 (hole3 _ _ _ _ _ _ _ a Hlt)
                               with
                               | inl pfail => inl pfail
                               | inr (rSibs, existT _ input'' Hle'') =>
                                 inr (lSib :: rSibs, existT _ input'' (length_lt_eq_trans _ _ _ _ Hle'' Hle))
                               end
                             | right Heq =>
                               match parseForest tbl gamma' input vis
                                                 (hole4 _ _ _ _ _ _ a Hg)
                               with
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
      parseTree tbl (T y) input vis a = inr (tr, rem)
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
      parseTree tbl (NT x) input vis a = inr (tr, rem)
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

  Ltac dm :=
    match goal with
    | H : context[match ?X with _ => _ end] |- _ => destruct X
    | |- context[match ?X with _ => _ end] => destruct X
    end.

  Ltac dms :=
    repeat (simpl in *; subst;
            match goal with
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
            end).
  
  Ltac invh :=
    match goal with
    | H : inr _ = inr _ |- _ => inv H
    end.

  Ltac invhs := repeat invh.

  Ltac cr :=
    repeat match goal with
           (* safe inversions *)
           | H : inr _ = inr _ |- _ => inv H
           | H : length_lt_eq _ _ _ |- _ => destruct H; subst

           (* we want to handle these cases manually *)                                
           | H : context[match parseTree _ _ _ _ _ with _ => _ end = _] |- _ =>
             idtac
           | H : context[match parseForest _ _ _ _ _ with _ => _ end = _] |- _ =>
             idtac
           | |- context[match parseTree _ _ _ _ _ with _ => _ end = _] =>
             idtac
           | |- context[match parseForest _ _ _ _ _ with _ => _ end = _] =>
             idtac
               
           | _ => simpl in *; subst; dm; tc; auto
           end.

  Ltac dlle := match goal with
               | H : length_lt_eq _ _ _ |- _ => destruct H; subst
               end.

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
                     \/ nullable_gamma g gamma); intros; destruct a.

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

  (*
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
   *)

  Lemma parseTree_sound' :
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
                       (input rem : list terminal)
                       Hle
                       (vis : NtSet.t)
                       (a   : Acc triple_lt (meas tbl input vis (G_arg gamma))),
                  parseForest tbl gamma input vis a = inr (f, existT _ rem Hle)
                  -> exists word,
                    word ++ rem = input
                    /\ gamma_derives_prefix gamma word f rem); intros; destruct a.

    - dms; tc.
      + invh.
        eexists; split; eauto.
        rewrite <- cons_app_singleton; auto.
      + dm; dms; tc.

    - dms; tc.
      step_eq Hpf; tc; dms; invh.
      apply IHpf in Hpf; clear IHpf.
      destruct Hpf as [word [Happ Hg]]; subst.
      eexists; split; eauto.
      apply Htbl in e; destruct e; eauto.

    - dms.
      + invh.
        eexists; split; auto.
        rewrite app_nil_l; auto.
      + dm; tc.
        dms; dm; dms; tc.

    - dms; tc.
      step_eq Hp; dms; tc.
      + step_eq Hpf; tc; dms; invh.
        apply IHp in Hp; clear IHp.
        apply IHpf in Hpf; clear IHpf.
        destruct Hp  as [wpre [Happ Hs]]; subst.
        destruct Hpf as [wsuf [Happ Hg]]; subst.
        exists (wpre ++ wsuf); split; auto.
        rewrite app_assoc; auto.
      + step_eq Hpf; tc; dms; invh.
        apply IHp in Hp; clear IHp.
        apply IHpf in Hpf; clear IHpf.
        destruct Hp as [wpre [Happ Hs]].
        apply l_ident_eq_nil in Happ; subst.
        destruct Hpf as [wsuf [Happ Hg]]; subst.
        exists ([] ++ wsuf); split; auto.
  Qed.      

  Lemma parse_sound :
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
        -> (@sym_derives_prefix g) sym word tr rem.
  Proof.
    intros g tbl Htbl tr sym word rem Hle vis a Hp.
    pose proof Hp as Hp'.
    eapply parseTree_sound' in Hp; eauto.
    destruct Hp as [word' [Happ Hder]].
    apply app_inv_tail in Happ.
    subst; auto.
  Qed.

End ParserSoundnessFn.

