Require Import Bool List String.

Require Import Grammar Lib.Utils.
Import ListNotations.
Open Scope string_scope.

Record subparser :=
  mkSp { busy       : list symbol ; (* use a set instead? *)
         syms       : list symbol ;
         input      : list string ;
         prediction : list symbol ;
         stack      : list (list symbol) }.

Definition rhss (g : grammar) (x : string) :=
  map snd (filter (fun prod => beqSym (fst prod) (NT x)) g).

Definition moveSubparser (g  : grammar)
                         (sp : subparser) :
                         list subparser :=
  let (busy, syms, input, prediction, stack) := sp in
  match syms with
  | nil =>
    match (stack, busy) with
    | (nil, nil) => [sp]
    | (k :: stack', b :: busy') => [mkSp busy' k input prediction stack']
    | _ => [mkSp nil nil ["implementation error"] nil nil]
    end
  | T y :: syms' =>
    match input with
    | nil => nil
    | token :: input' =>
      match beqSym (T y) (T token) with
      | false => nil
      | true => [mkSp nil syms' input' prediction stack]
      end
    end
  | NT x :: k =>
    match find (beqSym (NT x)) busy with
    | Some _ => nil (* changed from [sp] *)
    | None =>
      let mkSp' := fun gamma => mkSp (NT x :: busy) 
                                     gamma 
                                     input 
                                     prediction 
                                     (k :: stack) in
      let xGammas := rhss g x in
      map mkSp' xGammas
    end
  end.

Definition startState g x input :=
  let xGammas := rhss g x in
  map (fun gamma =>
         mkSp [NT x] gamma input gamma [[]]) xGammas.

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
    if existsb (fun sp2 => 
                  beqList sp.(syms) sp2.(syms) && 
                  beqStack sp.(stack) sp2.(stack) &&
                  negb (beqList sp.(prediction) sp2.(prediction))) sps'
    then true
    else conflict sps'
  end.

Inductive sll_result := 
| Choice   : list symbol -> sll_result
| Conflict : list subparser -> sll_result
| Fail     : sll_result.  

Fixpoint sllPredict g sps fuel :=
  match fuel with
  | O => Fail
  | S n =>
    let predictions := map prediction sps in
    match nub predictions beqList with
    | nil => Fail
    | [p] => Choice p
    | _ => if conflict sps then
             Conflict sps
           else 
             sllPredict g (target g sps) n
    end
  end.

Definition adaptivePredict g x input :=
  sllPredict g (startState g x input) 100.
             