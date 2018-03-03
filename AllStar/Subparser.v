Require Import Bool List Omega String Program.Wf.
Require Import Grammar Lib.Lemmas Lib.Tactics Lib.Utils.
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

(* Advance a single subparser as far as possible without
   consuming an input symbol *)
Program Fixpoint spClosure
        (g : grammar) (freeSyms : SymbolSet.t) (sp : subparser)
        {measure (SymbolSet.cardinal freeSyms)}
        : list subparser :=
  match sp.(stack) with
  | nil => [sp]
  | T _ :: _ => [sp]
  | NT x :: stack' => 
    match removeOpt (NT x) freeSyms with
    | None => nil (* recursion detected *)
    | Some freeSyms' =>
      let newSps :=
          map (fun gamma => mkSp (gamma ++ stack') sp.(pred))
              (rhss g x)
      in  concat (map (fun sp => spClosure g freeSyms' sp)
                      newSps)
    end
  end.
Obligation 1.
eapply removeOptDecreasing. symmetry. eassumption.
Qed.

Definition closure
           (g : grammar) (freeSyms : SymbolSet.t)
           (sps : list subparser) : list subparser :=
  concat (map (spClosure g freeSyms) sps).

(* LL predict when stack0 is nil, SLL predict otherwise *)
Definition startState g x stack0 :=
  let sps := map (fun gamma =>
                    mkSp (gamma ++ stack0) gamma)
                 (rhss g x)
  in  closure g (nonterminals g) sps.

Definition target
           (g : grammar) (sps : list subparser)
           (token : string) : list subparser :=
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

(* Here's the beginning of another way to prove termination
   based on the length of a list *)
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
