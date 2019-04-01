Require Import PeanoNat.
Require Import String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Grammar.
Require Import Parser.
Require Import Main.

Open Scope string_scope.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module NatStringTypes <: SYMBOL_TYPES.
    Definition terminal := string.
    Definition nonterminal := nat.
    Definition literal := string.
    Definition t_eq_dec := string_dec.
    Definition nt_eq_dec := Nat.eq_dec.
End NatStringTypes.

(* Next, we generate grammar definitions for those types. *)
Module Export NatStringGrammar <: T.
  Module SymTy := NatStringTypes.
  Module Defs  := DefsFn SymTy.
  Export SymTy.
  Export Defs.
End NatStringGrammar.


Definition value  := 0.
Definition pairs  := 1.
Definition pairs' := 2.
Definition pair   := 3.
Definition elts   := 4.
Definition elts'  := 5.

(* Now we can define a grammar as a record 
   containing a start symbol and a list of productions. *)
Definition g : grammar :=
  {| start := value
  ; prods :=
      [ (value, [T "{"; NT pairs; T "}"])
      ; (value, [T "["; NT elts; T "]"])
      ; (value, [T "STRING"])
      ; (value, [T "INT"])
      ; (value, [T "FLOAT"])
      ; (value, [T "TRUE"])
      ; (value, [T "FALSE"])
      ; (value, [T "NULL"])
          
      ; (pairs, [])
      ; (pairs, [NT pair; NT pairs'])
          
      ; (pairs', [])
      ; (pairs', [T ","; NT pair; NT pairs'])

      ; (pair, [T "STRING"; T ":"; NT value])

      ; (elts, [])
      ; (elts, [NT value; NT elts'])

      ; (elts', [])
      ; (elts', [T ","; NT value; NT elts'])
      ]
  |}.

(* The parser generator itself. *)
Module Export PG := Main NatStringGrammar.

Extraction "vermillion_defs.ml" g parseTableOf parse.