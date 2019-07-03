Require Import PeanoNat.
Require Import String.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

Require Import Grammar.
Require Import Parser.
Require Import Main.

Open Scope string_scope.

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
  | Int 
  | Float 
  | Str 
  | Tru 
  | Fls 
  | Null 
  | LeftBrace 
  | RightBrace 
  | LeftBrack
  | RightBrack
  | Colon
  | Comma.
  
  Definition terminal := terminal'.
  
  Inductive nonterminal' :=
  | Value 
  | Pairs
  | PairsTl
  | Pair 
  | Elts
  | EltsTl.
  
  Definition nonterminal := nonterminal'.

  Lemma t_eq_dec : forall (t t' : terminal),
      {t = t'} + {t <> t'}.
  Proof. decide equality. Defined.
  
  Lemma nt_eq_dec : forall (nt nt' : nonterminal),
      {nt = nt'} + {nt <> nt'}.
  Proof. decide equality. Defined.

  Definition show_t (a : terminal) : string :=
    match a with
    | Int        => "Int"
    | Float      => "Float"
    | Str        => "String"
    | Tru        => "True"
    | Fls        => "False"
    | Null       => "Null"
    | LeftBrace  => "{"
    | RightBrace => "}" 
    | LeftBrack  => "["
    | RightBrack => "]"
    | Colon      => ":"
    | Comma      => ","
    end.

  Definition show_nt (x : nonterminal) : string :=
    match x with
    | Value    => "value"
    | Pairs    => "pairs"
    | PairsTl  => "pairs_tl"
    | Pair     => "pair"
    | Elts     => "elts"
    | EltsTl   => "elts_tl"
    end.
  
  Definition t_semty (a : terminal) : Type :=
    match a with
    | Int   => nat
    | Float => nat
    | Str   => string
    | _     => unit
    end.

  Definition nt_semty (x : nonterminal) : Type :=
    match x with
    | Value   => jvalue
    | Pairs   => list (string * jvalue)
    | PairsTl => list (string * jvalue)
    | Pair    => string * jvalue
    | Elts    => list jvalue
    | EltsTl  => list jvalue
    end.

End Json_Types.

(* Next, we generate grammar definitions for those types,
   and we package the types and their accompanying defs
   into a single module *)
Module Export G <: Grammar.T.
  Module Export SymTy := Json_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

(* The parser generator itself. *)
Module Export PG := Make G.

(* Now we can define a grammar as a record 
   containing a start symbol and a list of productions. *)
Definition jsonGrammar : grammar :=
  {| start := Value
  
   ; prods := [ existT action_ty
                       (* association list rule *)
                       (Value, [T LeftBrace; NT Pairs; T RightBrace])
                       (fun tup => match tup with
                                   | (_, (prs, (_, _))) => JAssoc prs
                                   end)
                       
              ; existT action_ty
                       (* list rule *)
                       (Value, [T LeftBrack; NT Elts; T RightBrack])
                       (fun tup => match tup with
                                   | (_, (es, (_, _))) => JList es
                                   end)

              ; existT action_ty
                       (* string rule *)
                       (Value, [T Str])
                       (fun tup => match tup with
                                   | (s, _) => JString s
                                   end)

              ; existT action_ty
                       (* int rule *)
                       (Value, [T Int])
                       (fun tup => match tup with
                                   | (n, _) => JInt n
                                   end)

              ; existT action_ty
                       (* float rule *)
                       (Value, [T Float])
                       (fun tup => match tup with
                                   | (n, _) => JFloat n
                                   end)

              ; existT action_ty
                       (* true rule *)
                       (Value, [T Tru])
                       (fun _ => JBool true)

              ; existT action_ty
                       (* false rule *)
                       (Value, [T Fls])
                       (fun _ => JBool false)

              ; existT action_ty
                       (* null rule *)
                       (Value, [T Null])
                       (fun _ => JNull)

              ; existT action_ty
                       (Pairs, [])
                       (fun _ => [])

              ; existT action_ty
                       (Pairs, [NT Pair; NT PairsTl])
                       (fun tup => match tup with
                                   | (pr, (prs, _)) => pr :: prs
                                   end)

              ; existT action_ty
                       (PairsTl, [])
                       (fun _ => [])

              ; existT action_ty
                       (PairsTl, [T Comma; NT Pair; NT PairsTl])
                       (fun tup => match tup with
                                   | (_, (pr, (prs, _))) => pr :: prs
                                   end)

              ; existT action_ty
                       (Pair, [T Str; T Colon; NT Value])
                       (fun tup => match tup with
                                   | (s, (_, (v, _))) => (s, v)
                                   end)

              ; existT action_ty
                       (Elts, [])
                       (fun _ => [])

              ; existT action_ty
                       (Elts, [NT Value; NT EltsTl])
                       (fun tup => match tup with 
                                   | (v, (vs, _)) => v :: vs
                                   end)

              ; existT action_ty
                       (EltsTl, [])
                       (fun _ => [])

              ; existT action_ty
                       (EltsTl, [T Comma; NT Value; NT EltsTl])
                       (fun tup => match tup with
                                   | (_, (v, (vs, _))) => v :: vs
                                   end)
                
              ]
  |}.

(* Non-dependent token representation for converting between Menhir and Vermillion tokens *)
Inductive simply_typed_token :=
  | StInt   : nat    -> simply_typed_token
  | StFloat : nat    -> simply_typed_token
  | StStr   : string -> simply_typed_token
  | StTru
  | StFls 
  | StNull 
  | StLeftBrace 
  | StRightBrace 
  | StLeftBrack
  | StRightBrack
  | StColon
  | StComma.

Definition depTokenOfSimplyTypedToken (stt : simply_typed_token) : token :=
  match stt with
  | StInt n      => existT _ Int n
  | StFloat n    => existT _ Float n
  | StStr s      => existT _ Str s
  | StTru        => existT _ Tru tt
  | StFls        => existT _ Fls tt
  | StNull       => existT _ Null tt
  | StLeftBrace  => existT _ LeftBrace tt
  | StRightBrace => existT _ RightBrace tt
  | StLeftBrack  => existT _ LeftBrack tt
  | StRightBrack => existT _ RightBrack tt
  | StColon      => existT _ Colon tt
  | StComma      => existT _ Comma tt
  end.

Extraction "vermillionJsonParser.ml" jsonGrammar parseTableOf parse depTokenOfSimplyTypedToken.
