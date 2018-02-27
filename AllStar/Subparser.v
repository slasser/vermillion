Require Import Bool List Omega String.
Require Import Grammar Lib.Utils Lib.Tactics.
Import ListNotations.
Open Scope string_scope.

Record subparser :=
  mkSp { stack      : list symbol ;
         prediction : list symbol }.

Definition beqSp sp sp2 :=
  beqList sp.(stack) sp2.(stack) &&
  beqList sp.(prediction) sp2.(prediction).

Definition move (token : string)
                (sps   : list subparser) 
                : list subparser :=
  let moveSp sp := 
      match sp.(stack) with
      | nil => [sp]
      | NT _ :: _ => nil (* implementation error? *)
      | T y :: stack' =>
        if beqSym (T y) (T token) then 
          [mkSp stack' sp.(prediction)] 
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

(* Should be able to get rid of fuel because freeSyms is decreasing *)
Fixpoint closure g freeSyms fuel sps :=
  match fuel with 
  | O => nil
  | S n => concat (map (spClosure g freeSyms n) sps)
  end
with spClosure g freeSyms fuel sp :=
       match fuel with 
       | O => nil
       | S n => 
         match sp.(stack) with
         | nil => [sp]
         | T _ :: _ => [sp]
         | NT x :: stack' => 
           match removeOpt (NT x) freeSyms beqSym with
           | None => nil (* recursion detected *)
           | Some freeSyms' =>
             let gammas := rhss g x in
             let newSps := map (fun gamma => 
                                  mkSp (gamma ++ stack') sp.(prediction)) gammas
             in closure g freeSyms' n newSps
           end
         end
       end.

Definition nonterminals g :=
  let prodNTs p :=
      match p with
      | (l, rs) => l :: filter isNT rs
      end
  in  concat (map prodNTs g).

(* Remove fuel from the call to closure! *)
Definition startState g x stack0 :=
  let gammas := rhss g x in
  let sps    := map (fun gamma =>
                       mkSp (gamma ++ stack0) gamma) gammas
  in  closure g (nonterminals g) 100 sps.

Definition target g sps (token : string) :=
  closure g (nonterminals g) 100 (move token sps).

Fixpoint conflict sps : bool :=
  match sps with
  | nil => false
  | sp :: sps' => 
    if existsb
         (fun sp2 => 
            beqList sp.(stack) sp2.(stack) && 
            negb (beqList sp.(prediction)                                                sp2.(prediction)))
         sps'
    then true
    else conflict sps'
  end.

Inductive prediction_result := 
| Choice   : list symbol -> prediction_result
| Conflict : list subparser -> prediction_result
| Fail     : prediction_result.  

(* LL predict when initial stacks are nil,
   SLL predict otherwise *)
Fixpoint predict g sps input :=
  let predictions := map prediction sps in
  match nub predictions beqList with
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
  let sllPrediction :=
      predict g (startState g x nil) input
  in  match sllPrediction with
      | Conflict _ =>
        predict g (startState g x stack0) input
      | _ => sllPrediction
      end.

