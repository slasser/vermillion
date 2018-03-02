Require Import Bool List Omega String Program.Wf.
Require Import Grammar Lib.Utils Lib.Tactics.
Import ListNotations.
Open Scope string_scope.

Record subparser :=
  mkSp { stack: list symbol ;
         pred : list symbol }.

(* Two subparsers are equal if their stacks and predictions are equal. *)
Definition beqSp sp sp2 :=
  beqList sp.(stack) sp2.(stack) &&
  beqList sp.(pred) sp2.(pred).

Definition move (token : string)
                (sps   : list subparser) 
                : list subparser :=
  let moveSp sp := 
      match sp.(stack) with
      | nil => [sp]
      | NT _ :: _ => nil (* implementation error? *)
      | T y :: stack' =>
        if beqSym (T y) (T token) then 
          [mkSp stack' sp.(pred)] 
        else 
          nil
      end 
  in  concat (map moveSp sps).

Definition removeOpt (x : symbol) (s : SymbolSet.t) :=
  if SymbolSet.mem x s then Some (SymbolSet.remove x s) else None.

Lemma empty_nil : forall s,
    SymbolSet.Empty s <-> SymbolSet.elements s = [].
Proof. 
  intros; split; intros.
  - destruct (SymbolSet.elements s) as [| e es] eqn:Hs.
    + reflexivity.
    + exfalso. 
      unfold SymbolSet.Empty in H; eapply H; clear H.
      assert (SetoidList.InA eq e (SymbolSet.elements s)).
      { rewrite Hs; constructor; reflexivity. }
      eapply SymbolSetFacts.elements_iff. eassumption.
  - unfold SymbolSet.Empty; unfold not; intros e Hin.
    rewrite SymbolSetFacts.elements_iff in Hin. 
    rewrite H in Hin. inv Hin.
Qed.

Lemma list_remove_le : forall (x : symbol) (ys : list symbol),
    List.length (remove symbol_eq_dec x ys) <= List.length ys.
Proof.
  intros. induction ys as [| y ys]; simpl.
  - reflexivity.
  - destruct (symbol_eq_dec x y); simpl; omega.
Qed.

Lemma list_remove_lt : forall (x : symbol) (ys : list symbol),
    List.In x ys -> 
    List.length (remove symbol_eq_dec x ys) < List.length ys.
Proof.
  intros. induction ys as [| y ys]; simpl.
  - inv H.
  - destruct (symbol_eq_dec x y) as [Heq | Hneq]; simpl.
    + pose proof list_remove_le as Hle.
      specialize Hle with (x := x) (ys := ys). omega.
    + apply lt_n_S. apply IHys. clear IHys.
      simpl in H. destruct H as [Hhd | Htl].
      * exfalso. apply Hneq. symmetry. assumption.
      * assumption.
Qed.

Lemma cardinal_length : forall s s',
    SymbolSet.cardinal s' < SymbolSet.cardinal s <-> 
    List.length (SymbolSet.elements s') < List.length (SymbolSet.elements s).
Proof.
  intros. split; intros.
  - repeat rewrite <- SymbolSet.cardinal_spec. assumption.
  - repeat rewrite SymbolSet.cardinal_spec. assumption.
Qed.

Lemma remove_not_In : forall x ys,
    ~In x ys <-> remove symbol_eq_dec x ys = ys.
Proof.
  intros; split; unfold not; intros.
  - induction ys; simpl.
    + reflexivity.
    + destruct (symbol_eq_dec x a); simpl.
      * exfalso. subst. apply H. apply in_eq.
      * assert (Htls : remove symbol_eq_dec x ys = ys).
      { apply IHys; intros; clear IHys.
        apply H. apply in_cons. assumption. }
      rewrite Htls; reflexivity.
  - rewrite <- H in H0. eapply remove_In. eassumption.
Qed.             

(* HERE is the lemma I needed -- wish I'd found remove_cardinal_1 sooner...*)
Lemma removeOptDecreasing : forall (x : symbol) (s s' : SymbolSet.t),
    removeOpt x s = Some s' ->
    SymbolSet.cardinal s' < SymbolSet.cardinal s.
Proof.
  intros. unfold removeOpt in H. 
  destruct (SymbolSet.mem x s) eqn:Hmem.
  - inv H.
    pose proof SymbolSetEqProps.remove_cardinal_1.
    apply H in Hmem. omega.
  - inv H.
Qed.

(* if removeOpt x l  = Some l', l' is a sublist of l *)
Fixpoint removeOpt' {A} (x : A) (l : list A) (beq : A -> A -> bool) :=
  match l with
  | nil => None
  | y :: l' => 
    if beq x y then
      Some l'
    else
      match removeOpt' x l' beq with
      | None => None
      | Some l'' => Some (y :: l'')
      end
  end.

(* ... and here's the proof: *)
Lemma removeOpt'Decreasing : forall A (x : A) beq (ys zs : list A),
    removeOpt' x ys beq = Some zs ->
    List.length zs < List.length ys.
Proof.
  induction ys as [| y ys]; intros zs H.
  - inversion H.
  - simpl in H.
    destruct (beq x y).
    + inv H; simpl; omega.
    + destruct (removeOpt' x ys beq).
      * inv H. simpl.
        apply lt_n_S; apply IHys; reflexivity.
      * inv H.
Qed.

Program Fixpoint spClosure (g : grammar)
                           (freeSyms : list symbol)
                           (sp : subparser) 
                           {measure (List.length freeSyms)}
                           : list subparser :=
       match sp.(stack) with
       | nil => [sp]
       | T _ :: _ => [sp]
       | NT x :: stack' => 
         match removeOpt' (NT x) freeSyms beqSym with
         | None => nil (* recursion detected *)
         | Some freeSyms' => 
           concat (map (fun gamma => 
                          spClosure g freeSyms' (mkSp (gamma ++ stack') sp.(pred)))
                       (rhss g x))
         end
       end.
Obligation 1.
eapply removeOpt'Decreasing. symmetry. eassumption.
Qed.

Definition nonterminals g :=
  let prodNTs p :=
      match p with
      | (l, rs) => l :: filter isNT rs
      end
  in  concat (map prodNTs g).

Definition closure (g : grammar) 
                   (freeSyms : list symbol) 
                   (sps : list subparser)
                   : list subparser :=
  concat (map (spClosure g freeSyms) sps).

(* LL predict when stack0 is nil, SLL predict otherwise *)
Definition startState g x stack0 :=
  let sps := map (fun gamma =>
                    mkSp (gamma ++ stack0) gamma) (rhss g x)
  in  closure g (nonterminals g) sps.

Definition target g sps (token : string) :=
  closure g (nonterminals g) (move token sps).

Fixpoint conflict sps : bool :=
  match sps with
  | nil => false
  | sp :: sps' => 
    if existsb
         (fun sp2 => 
            beqList sp.(stack) sp2.(stack) && 
            negb (beqList sp.(pred) sp2.(pred)))
         sps'
    then true
    else conflict sps'
  end.

Inductive pred_result := 
| Choice   : list symbol -> pred_result
| Conflict : list subparser -> pred_result
| Fail     : pred_result.  

Fixpoint predict g sps input :=
  let preds := map pred sps in
  match nub preds beqList with
  | nil => Fail
  | [p] => Choice p
  | _ => if conflict sps then
           Conflict sps
         else
           match input with
           | nil => Fail (*actually, check for final configs*)
           | token :: input' => 
             predict g (target g sps token) input'
           end
  end.

Definition adaptivePredict g x input stack0 :=
  let sllPred :=
      predict g (startState g x nil) input
  in  match sllPred with
      | Conflict _ =>
        predict g (startState g x stack0) input
      | _ => sllPred
      end.


Section lengthorder.
  Variable A : Type.
  
  Definition lengthOrder (xs ys : list A) :=
    List.length xs < List.length ys.
  
  Lemma lengthOrder_wf' : 
    forall len ys, List.length ys <= len -> Acc lengthOrder ys.
  Proof. 
    induction len; intros ys H_length_ys; apply Acc_intro; intros xs H_xs_ys.
    - unfold lengthOrder in H_xs_ys. omega.
    - apply IHlen. unfold lengthOrder in H_xs_ys. omega.
  Defined.
  
  Theorem lengthOrder_wf : well_founded lengthOrder.
  Proof.
    unfold well_founded. intro ys.
    apply lengthOrder_wf' with (len := List.length ys). omega.
  Defined.
  
End lengthorder.

