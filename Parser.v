Require Import FMaps List MSets Omega String Program.Wf Arith.Wf_nat.
Require Import Grammar.
Require Import Lemmas.
Require Import Tactics.
Import ListNotations.
Open Scope string_scope.

Module ParserFn (Import G : Grammar.T).
  Module Import L := LemmasFn G.
  
  Definition t_eq_dec  := G.SymTy.t_eq_dec.
  Definition nt_eq_dec := G.SymTy.nt_eq_dec.
  
  Section TripleLT.
    
    Variables (A B C : Type) (ltA : relation A) (ltB : relation B) (ltC : relation C).
    
    Inductive triple_lex : A * B * C -> A * B * C -> Prop :=
    | fst_lt : forall x x' y y' z z', ltA x x' -> triple_lex (x, y, z) (x', y', z')
    | snd_lt : forall x y y' z z', ltB y y' -> triple_lex (x, y, z) (x, y', z')
    | thd_lt : forall x y z z', ltC z z' -> triple_lex (x, y, z) (x, y, z').
    
    Hint Constructors triple_lex.
    
    Theorem triple_lex_trans :
      transitive _ ltA -> transitive _ ltB -> transitive _ ltC -> transitive _ triple_lex.
    Proof.
      intros tA tB tC [[x1 y1] z1] [[x2 y2] z2] [[x3 y3] z3] H12 H23.
      inv H12; inv H23; eauto.
    Defined.
    
    Theorem triple_lex_wf :
      well_founded ltA -> well_founded ltB -> well_founded ltC -> well_founded triple_lex.
    Proof.
      intros wfA wfB wfC [[x y] z].
      revert y z.
      induction (wfA x) as [x _ IHx].
      intros y.
      induction (wfB y) as [y _ IHy].
      intros z.
      induction (wfC z) as [z _ IHz].
      constructor.
      intros [[x' y'] z'] H.
      inv H; eauto.
    Defined.
    
  End TripleLT.
  
  Inductive sym_arg  :=
  | F_arg : symbol -> sym_arg
  | G_arg : list symbol -> sym_arg.

  Definition sa_size (sa : sym_arg) : nat :=
    match sa with
    | F_arg _ => 0
    | G_arg gamma => 1 + List.length gamma
    end.
  
  Definition nt_keys (tbl : parse_table) : list nonterminal :=
    List.map (fun pr => match pr with 
                        | ((x, _), _) => x
                        end)
             (ParseTable.elements tbl).
  
  Lemma not_in_list_iff_not_in_fromNtList:
    forall (x : NtSet.elt) (l : list NtSet.elt),
      ~ In x l <-> ~ NtSet.In x (fromNtList l).
  Proof.
    split; unfold not; intros H1 H2.
    - apply H1.
      apply in_list_iff_in_fromNtList; auto.
    - apply H1.
      apply in_list_iff_in_fromNtList; auto.
  Defined.
  
  Lemma lt_trans : transitive nat lt.
  Proof.
    red.
    apply Nat_as_DT.lt_trans.
  Defined.
  
  Lemma pt_lookup_in_nt_keys :
    forall x la tbl gamma,
      pt_lookup x la tbl = Some gamma
      -> In x (nt_keys tbl).
  Proof.
    intros.
    unfold nt_keys.
    apply pt_lookup_elements in H.
    induction (ParseTable.elements tbl).
    - inv H.
    - simpl in *.
      destruct H.
      + subst; auto.
      + right; auto.
  Defined.

  Lemma cardinal_diff_add_lt :
    forall x la gamma vis tbl,
      pt_lookup x la tbl = Some gamma
      -> ~ NtSet.In x vis
      -> NtSet.cardinal
           (NtSet.diff (fromNtList (nt_keys tbl))
                       (NtSet.add x vis)) <
         NtSet.cardinal
           (NtSet.diff (fromNtList (nt_keys tbl)) vis).
  Proof.
    intros.
    apply NP.subset_cardinal_lt with (x := x); try ND.fsetdec.
    apply in_A_not_in_B_in_diff; auto.
    apply in_list_iff_in_fromNtList.
    eapply pt_lookup_in_nt_keys; eauto.
  Defined.
  
  Definition ptlk_dec x la tbl : Datatypes.sum (pt_lookup x la tbl = None)
                                               {gamma | pt_lookup x la tbl = Some gamma}.
    destruct (pt_lookup x la tbl) eqn:Hlk.
    - right.
      econstructor; eauto.
    - left.
      auto.
  Defined.
  
  Definition meas tbl (tokens : list token) (vis : NtSet.t) (sa : sym_arg) :=
    (List.length tokens,
     NtSet.cardinal (NtSet.diff (fromNtList (nt_keys tbl)) vis),
     sa_size sa).
  
  Definition triple_lt : relation (nat * nat * nat) :=
    triple_lex nat nat nat lt lt lt.
  
  Theorem triple_lt_wf : well_founded triple_lt.
    apply triple_lex_wf; try apply lt_wf.
  Defined.
  
  Lemma hole1 :
    forall tbl tokens vis sa sa' x gamma,
      Acc triple_lt (meas tbl tokens vis sa)
      -> pt_lookup x (peek tokens) tbl = Some gamma
      -> ~ NtSet.In x vis
      -> Acc triple_lt (meas tbl tokens (NtSet.add x vis) sa').
  Proof.
    intros.
    eapply Acc_inv; eauto.
    unfold meas.
    apply snd_lt; simpl.
    eapply cardinal_diff_add_lt; eauto.
  Defined.
  
  Lemma hole2 :
    forall tbl tokens vis gamma sym,
      Acc triple_lt (meas tbl tokens vis (G_arg gamma))
      -> Acc triple_lt (meas tbl tokens vis (F_arg sym)).
  Proof.
    intros.
    eapply Acc_inv; eauto.
    apply thd_lt; simpl; omega.
  Defined.
  
  Lemma hole3 :
    forall tbl tokens tokens' vis vis' sa sa',
      Acc triple_lt (meas tbl tokens vis sa)
      -> List.length tokens' < List.length tokens
      -> Acc triple_lt (meas tbl tokens' vis' sa').
  Proof.
    intros.
    eapply Acc_inv; eauto.
    apply fst_lt; auto.
  Defined.
  
  Lemma hole4 :
    forall tbl tokens vis gamma sym gamma',
      Acc triple_lt (meas tbl tokens vis (G_arg gamma))
      -> sym :: gamma' = gamma
      -> Acc triple_lt (meas tbl tokens vis (G_arg gamma')).
  Proof.
    intros.
    eapply Acc_inv; eauto.
    apply thd_lt; subst; simpl; omega.
  Defined.
  
  Open Scope list_scope.
  
  Lemma l_ident_eq_nil :
    forall A (xs ys : list A), xs ++ ys = ys -> xs = [].
  Proof.
    intros.
    rewrite <- app_nil_l in H.
    apply app_inv_tail in H; auto.
  Qed.
  
  Inductive parse_failure : Type :=
  | Reject   : string -> list token -> parse_failure
  | Error    : string -> nonterminal -> list token -> parse_failure.
  
  Definition mem_dec (x : nonterminal) (s : NtSet.t) :
                     {NtSet.In x s} + {~ NtSet.In x s}.
    destruct (NtSet.mem x s) eqn:Hm.
    - left.
      apply NtSet.mem_spec; auto.
    - right.
      unfold not; intros H.
      apply NtSet.mem_spec in H.
      congruence.
  Defined.
  
  Definition length_lt_eq A (xs ys : list A) :=
    {List.length xs < List.length ys} + {xs = ys}.
  
  Lemma length_lt_eq_cons : forall A xs (x : A) xs',
      xs = x :: xs'
      -> length_lt_eq A xs' xs.
  Proof.
    intros; simpl; red; subst; auto.
  Defined.
  
  Lemma length_lt_eq_refl : forall A (xs : list A),
      length_lt_eq A xs xs.
  Proof.
    intros; simpl; red; auto.
  Defined.
  
  Lemma length_lt_eq_trans :
    forall A (xs ys zs : list A),
      length_lt_eq A xs ys
      -> length_lt_eq A ys zs
      -> length_lt_eq A xs zs.
  Proof.
    intros A xs ys zs H H'; unfold length_lt_eq in *;
      destruct H; destruct H'; subst; auto.
    left; omega.
  Defined.

  Definition mismatchMessage (a a' : terminal) : string :=
    "Token mismatch; expected " ++ show_t a ++ ", saw " ++ show_t a'.
  
  Fixpoint parseSymbol
           (tbl : parse_table)
           (sym : symbol)
           (ts  : list token)
           (vis : NtSet.t)
           (a : Acc triple_lt (meas tbl ts vis (F_arg sym)))
           {struct a}
    : Datatypes.sum parse_failure
                    (symbol_semty sym * {ts' & length_lt_eq _ ts' ts}) :=
    match sym with
    | T a =>
      match ts as l return ts = l -> _ with
      | [] =>
        fun _ => inl (Reject "input exhausted" ts)
      | (existT _ a' v') :: ts' =>
        fun Hts => match t_eq_dec a' a with
                   | left Heq =>
                     let v := eq_rect _ _ v' _ Heq in
                     inr (v, existT _ ts' (length_lt_eq_cons _ _ _ _ Hts))
                   | right _ =>
                     inl (Reject (mismatchMessage a a') ts)
                   end
      end eq_refl
    | NT x =>
      match mem_dec x vis with
      | left _ => inl (Error "left recursion detected" x ts)
      | right Hnin =>
        match ptlk_dec x (peek ts) tbl with
        | inl _ => inl (Reject "lookup failure" ts)
        | inr (exist _ (existT _ (x', gamma) f) Hlk) =>
          match nt_eq_dec x' x with
          | left Heq =>
            match parseGamma tbl gamma ts (NtSet.add x vis)
                              (hole1 _ _ _ _ _ _ _ a Hlk Hnin)
            with
            | inl pfail => inl pfail
            | inr (vs, existT _ ts' Hle) =>
              let v := eq_rect _ _ (f vs) _ Heq in
              inr (v, existT _ ts' Hle)
            end
          | right _ =>
            inl (Error "malformed parse table" x ts)
          end
        end
      end
    end
  with parseGamma (tbl   : parse_table)
                   (gamma : list symbol)
                   (ts    : list token)
                   (vis   : NtSet.t)
                   (a     : Acc triple_lt (meas tbl ts vis (G_arg gamma)))
                   {struct a}
       : Datatypes.sum parse_failure
                       (rhs_semty gamma * {ts' & length_lt_eq _ ts' ts}) :=
         match gamma as l return l = gamma -> _ with
         | nil =>
           fun Hg =>
             let vs := eq_rect _ _ tt _ Hg in
             inr (vs, existT (fun ts' => length_lt_eq _ ts' ts)
                             ts
                             (length_lt_eq_refl _ _))
         | sym :: gamma' =>
           fun Hg => 
             match parseSymbol tbl sym ts vis (hole2 _ _ _ _ _ a) with
             | inl pfail => inl pfail
             | inr (lSib, existT _ ts' Hle) =>
               match Hle with
               | left Hlt =>
                 match parseGamma tbl gamma' ts' NtSet.empty
                                   (hole3 _ _ _ _ _ _ _ a Hlt)
                 with
                 | inl pfail => inl pfail
                 | inr (rSibs, existT _ ts'' Hle'') =>
                   let vs := eq_rect _ _ (lSib, rSibs) _ Hg in
                   inr (vs, existT _ ts'' (length_lt_eq_trans _ _ _ _ Hle'' Hle))
                 end
               | right Heq =>
                 match parseGamma tbl gamma' ts vis
                                   (hole4 _ _ _ _ _ _ a Hg)
                 with
                 | inl pfail => inl pfail
                 | inr (rSibs, existT _ ts'' Hle'') =>
                   let vs := eq_rect _ _ (lSib, rSibs) _ Hg in
                   inr (vs, existT _ ts'' Hle'')
                 end
               end
             end
         end eq_refl.

End ParserFn.

