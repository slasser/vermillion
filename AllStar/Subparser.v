Require Import List String.
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