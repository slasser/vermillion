Require Import String.
Require Import Grammar.
Require Import Main.

(* This file gives an example of how to use Vermillion.

   The example is based on Grammar 3.11 from Appel's 
   "Modern Compiler Implementation in ML":

   S -> if E then S else S
   S -> begin S L
   S -> print E

   L -> end
   L -> ; S L

   E -> num = num 
*) 

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module G311_Types <: SYMBOL_TYPES.
  
  Inductive terminal' :=
  | If | Then | Else | Begin | Print | End | Semi | Num | Eq.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | S | L | E.
  
  Definition nonterminal := nonterminal'.
  
  Definition literal := string.
  
  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

End G311_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export G <: Grammar.T.
  Module SymTy := G311_Types.
  Module Defs  := DefsFn SymTy.
  Export SymTy.
  Export Defs.
End G.

(* Now we can represent the grammar from the textbook
   as a record with "start" and "prods" fields. *)
Definition g311 : grammar :=
  {| start := S ;
     prods := [(S, [T If; NT E; T Then; NT S; T Else; NT S]);
               (S, [T Begin; NT S; NT L]);
               (S, [T Print; NT E]);
                 
               (L, [T End]);
               (L, [T Semi; NT S; NT L]);
                 
               (E, [T Num; T Eq; T Num])]
  |}.

(* Now we create a module that gives us access to
   the top-level parser generator functions:

   parseTableOf : grammar -> option parse_table

   parse : parse_table -> symbol -> list terminal -> 
           sum parse_failure (tree * list terminal) *)
Module Import PG := Make G.

(* Example input to the parser *)
Definition example_prog :=
  [If; Num; Eq; Num; Then; Print; Num; Eq; Num; Else; Print; Num; Eq; Num].

(* Now we can generate an LL(1) parse table for the grammar
   and use it to parse the example input. *)
Compute (match parseTableOf g311 with
         | Some tbl => inr (parse tbl (NT S) example_prog)
         | None => inl "no correct LL(1) parse table"
         end).                             

