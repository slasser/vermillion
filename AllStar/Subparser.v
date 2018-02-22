Require Import Bool List String.
Require Import Grammar Lib.Utils.
Import ListNotations.

Record subparser :=
  mkSubparser { busy       : list symbol ; (* should be set *)
                syms       : list symbol ;
                input      : list string ;
                prediction : list symbol ;
                stack      : list (list symbol) }.

(* Maybe better to stick to lists of subparsers *)
(*
Definition subparser_eq_dec : forall (sub sub2 : subparser),
    {sub = sub2} + {~sub = sub2}.
Proof.
  intros. repeat decide equality.
Qed.

Module MDT_Subparser.
  Definition t := subparser.
  Definition eq_dec := subparser_eq_dec.
End MDT_Subparser.

Module SubparserAsDT := Make_UDT(MDT_Subparser).

Module SpSet := MSetWeakList.Make SubparserAsDT.
Module SpSetFacts := WFactsOn SubparserAsDT SpSet.
*)

Definition rhss (g : grammar) (x : string) :=
  map snd (filter (fun prod => beqSym (fst prod) (NT x)) g).

Definition moveSubparser (g : grammar)
                         (sp : subparser) :
                         list subparser :=
  let (busy, syms, input, prediction, stack) := sp in
  match syms with
  | nil =>
    match stack with
    | nil => [sp]
    | k :: stack' => [mkSubparser busy k input prediction stack']
    end
  | T y :: syms' =>
    match input with
    | nil => nil
    | token :: input' =>
      match beqSym (T y) (T token) with
      | false => nil
      | true => [mkSubparser busy syms' input' prediction stack]
      end
    end
  | NT x :: k =>
    match find (beqSym (NT x)) busy with
    | Some _ => [sp]
    | None =>
      let xGammas := rhss g x in
      let sps := map (fun gamma =>
                        mkSubparser (NT x :: busy)
                                    gamma
                                    input
                                    prediction
                                    (k :: stack)) xGammas
      in  sps
    end
  end.

Definition startState g x input :=
  let xGammas := rhss g x in
  map (fun gamma =>
         mkSubparser nil gamma input gamma nil) xGammas.

Definition target g sps :=
  concat (map (moveSubparser g) sps).

Definition elem {A : Type} (x : A) (l : list A) (cmp : A -> A -> bool) : bool :=
            match find (cmp x) l with
  | Some _ => true
  | None   => false
  end.

Definition nub {A : Type} (xs : list A) (cmp : A -> A -> bool) : list A :=
  fold_right (fun x acc => if elem x acc cmp then acc else x :: acc) nil xs.

Fixpoint beqList (xs : list symbol) (ys : list symbol) : bool :=
  match (xs, ys) with
  | (nil, nil) => true
  | (x :: xs', y :: ys') => if beqSym x y then beqList xs' ys' else false
  | _ => false
  end.

Fixpoint beqStack (xss yss : list (list symbol)) : bool :=
  match (xss, yss) with
  | (nil, nil) => true
  | (xs :: xss', ys :: yss') => if beqList xs ys then beqStack xss' yss' else false
  | _ => false
  end.

Fixpoint conflict sps : bool :=
  match sps with
  | nil => false
  | [sp] => false
  | sp :: sps' => 
    if existsb (fun sp2 => beqList sp.(syms) sp2.(syms) && beqStack sp.(stack) sp2.(stack)) sps' then
      true
    else 
      conflict sps'
  end.


Fixpoint sllPredict g sps fuel :=
  match fuel with
  | O => None
  | S n =>
    let predictions := map prediction sps in
    match nub predictions beqList with
    | nil => None
    | [p] => Some p
    | _ => if conflict sps then
             Some [T "conflict detected!"]
           else 
             sllPredict g (target g sps) n
    end
  end.

Definition adaptivePredict g x input :=
  sllPredict g (startState g x input) 100.
             