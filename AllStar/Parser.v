Require Import List MSets MSetDecide String.
Require Import Grammar ParseTree Vermillion.Lib.Utils.
Import ListNotations.

Definition adaptivePredict (g : grammar) (sym : symbol) (input : list string) : option (list symbol) :=
  Some [NT "foo"].

Fixpoint parse (g : grammar)
               (sym : symbol)
               (input : list string)
               (fuel : nat) :
               (option tree * list string) :=
  match fuel with
  | O => (None, input)
  | S n => 
    match (sym, input) with
    | (T _, nil) => (None, input)
    | (T y, token :: input') =>
      match beqSym (T y) (T token) with
      | false => (None, input)
      | true => (Some (Leaf y), input')
      end
    | (NT x, _) =>
      match adaptivePredict g sym input with
      | None => (None, input)
      | Some gamma =>
        match parseForest g gamma input n with
        | (None, _) => (None, input)
        | (Some sts, input') =>
          (Some (Node x sts), input')
        end
      end
    end
  end
with parseForest (g : grammar)
                 (gamma : list symbol)
                 (input : list string)
                 (fuel : nat) :
                 (option forest * list string) :=
       match fuel with
       | O => (None, input)
       | S n =>
         match gamma with
         | nil => (Some Fnil, input)
         | sym :: gamma' =>
           match parse g sym input n with
           | (None, _) => (None, input)
           | (Some lSib, input') =>
             match parseForest g gamma' input' n with
             | (None, _) => (None, input)
             | (Some rSibs, input'') =>
               (Some (Fcons lSib rSibs), input'')
             end
           end
         end
       end.