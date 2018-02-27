Require Import Bool List String.
Require Import Grammar Lib.Utils.
Import ListNotations.
Open Scope string_scope.

Record subparser :=
  mkSp { stack      : list symbol ;
         prediction : list symbol }.

Definition beqSp sp sp2 :=
  beqList sp.(stack) sp2.(stack) &&
  beqList sp.(prediction) sp2.(prediction).

Definition moveSp (g : grammar)
    (token : string) (sp : subparser) : list subparser :=
  match sp.(stack) with
  | nil => nil
  | NT _ :: _ => [sp]
  | T y :: stack' =>
    if beqSym (T y) (T token) then
      [mkSp stack' sp.(prediction)]
    else
      nil
  end.

Definition move (g : grammar) (sps : list subparser) (token : string) : list subparser :=
  concat (map (moveSp g token) sps).

Fixpoint spClosure (g    : grammar)
                   (busy : list subparser)
                   (fuel : nat)
                   (sp   : subparser)
                   : list subparser :=
  match fuel with
  | O => nil
  | S n => 
    if elem sp busy beqSp then
      nil
    else
      match sp.(stack) with
      | nil => [sp]
      | T _ :: _ => [sp]
      | NT x :: stack' =>
        let gammas := rhss g x in
        let newSps :=
            map (fun gamma =>
                   mkSp (gamma ++ stack') sp.(prediction))
                gammas
        in concat (map (spClosure g (sp :: busy) n) newSps)
      end
  end.

Definition closure (g : grammar) (sps : list subparser) :=
  concat (map (spClosure g nil 100) sps).

Definition startState g x stack0 :=
  let gammas := rhss g x in
  let sps    := map (fun gamma =>
                       mkSp (gamma ++ stack0) gamma) gammas
  in  closure g sps.

Definition target g sps (token : string) :=
  closure g (move g sps token ).

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

