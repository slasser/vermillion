Require Import PeanoNat.
Require Import String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Grammar.
Require Import Parser.
Require Import Main.

Open Scope string_scope.

(*

type value = [
  | `Assoc of (string * value) list
  | `Bool of bool
  | `Float of float
  | `Int of int
  | `List of value list
  | `Null
  | `String of string
  ]
*)

Inductive jvalue :=
| JAssoc  : list (string * jvalue) -> jvalue
| JBool   : bool -> jvalue
| JFloat  : nat -> jvalue
| JInt    : nat -> jvalue
| JList   : list jvalue -> jvalue
| JNull   : jvalue
| JString : string -> jvalue.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module Json_Types <: SYMBOL_TYPES.
  
  Inductive terminal' :=
  | T_int 
  | T_float 
  | T_string 
  | T_true 
  | T_false 
  | T_null 
  | T_left_brace 
  | T_right_brace 
  | T_left_brack 
  | T_right_brack 
  | T_colon 
  | T_comma.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | N_value 
  | N_pairs 
  | N_pairs_tl 
  | N_pair 
  | N_elts 
  | N_elts_tl.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition show_t (a : terminal) : string :=
    match a with
    | T_int         => "Int"
    | T_float       => "Float"
    | T_string      => "String"
    | T_true        => "True"
    | T_false       => "False"
    | T_null        => "Null"
    | T_left_brace  => "{"
    | T_right_brace => "}" 
    | T_left_brack  => "["
    | T_right_brack => "]"
    | T_colon       => ":"
    | T_comma       => ","
    end.

  Definition show_nt (x : nonterminal) : string :=
    match x with
    | N_value    => "value"
    | N_pairs    => "pairs"
    | N_pairs_tl => "pairs_tl"
    | N_pair     => "pair"
    | N_elts     => "elts"
    | N_elts_tl  => "elts_tl"
    end.
  
  Definition t_semty (a : terminal) : Type :=
    match a with
    | T_int         => nat
    | T_float       => nat
    | T_string      => string
    | _             => unit
    end.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | N_value    => jvalue
    | N_pairs    => list (string * jvalue)
    | N_pairs_tl => list (string * jvalue)
    | N_pair     => string * jvalue
    | N_elts     => list jvalue
    | N_elts_tl  => list jvalue
    end.

End Json_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export G <: Grammar.T.
  Module Export SymTy := Json_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

(* Now we can define a grammar as a record 
   containing a start symbol and a list of productions. *)
Definition jsonGrammar : grammar :=
  {| start := N_value ;
     prods := [existT action_ty
                      (N_value, [T T_left_brack; NT N_pairs; T T_right_brack])
                      (fun tup => match tup with
                                  | (_, (prs, (_, _))) =>
                                    JAssoc prs
                                  end)
              ]
  |}.

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