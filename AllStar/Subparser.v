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

(* if removeOpt x l  = Some l', l' is a sublist of l *)
Fixpoint removeOpt {A} (x : A) (l : list A) (beq : A -> A -> bool) :=
  match l with
  | nil => None
  | y :: l' => 
    if beq x y then
      Some l'
    else
      match removeOpt x l' beq with
      | None => None
      | Some l'' => Some (y :: l'')
      end
  end.

(* ... and here's the proof: *)
Lemma removeOptDecreasing : forall A (x : A) beq (ys zs : list A),
    removeOpt x ys beq = Some zs ->
    List.length zs < List.length ys.
Proof.
  induction ys as [| y ys]; intros zs H.
  - inversion H.
  - simpl in H.
    destruct (beq x y).
    + inv H; simpl; omega.
    + destruct (removeOpt x ys beq).
      * inv H. simpl.
        apply lt_n_S; apply IHys; reflexivity.
      * inv H.
Qed.

(* Here's a better way to handle removing elements from the free set. *)

Definition removeOpt' (x : symbol) (s : SymbolSet.t) :=
  let s' := SymbolSet.remove x s in
  if (SymbolSet.cardinal s') <? (SymbolSet.cardinal s) then
    Some s'
  else
    None.

Lemma removeOpt'Decreasing : forall (x : symbol) (ys zs : SymbolSet.t),
    removeOpt' x ys = Some zs ->
    SymbolSet.cardinal zs < SymbolSet.cardinal ys.
Proof.
  intros. unfold removeOpt' in H.
  destruct (SymbolSet.cardinal (SymbolSet.remove x ys) <? SymbolSet.cardinal ys)
           eqn:Heq.
  - inv H. rewrite <- Nat.ltb_lt. assumption.
  - inv H.
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
         match removeOpt (NT x) freeSyms beqSym with
         | None => nil (* recursion detected *)
         | Some freeSyms' => 
           concat (map (fun gamma => 
                          spClosure g freeSyms' (mkSp (gamma ++ stack') sp.(pred)))
                       (rhss g x))
         end
       end.
Obligation 1.
eapply removeOptDecreasing. symmetry. eassumption.
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

