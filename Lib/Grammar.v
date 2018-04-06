Require Import List String.
Require Import FMaps MSets.
Open Scope string_scope.
Import ListNotations.

Definition terminal := string.
Definition nonterminal := string.

Inductive symbol :=
  | T  : terminal -> symbol
  | NT : nonterminal -> symbol.

Definition production := (string * list symbol)%type.

Record grammar := { productions : list production;
                    start : string }.

Module MDT_String.
  Definition t := string.
  Definition eq_dec := string_dec.
End MDT_String.

Module StringAsDT := Make_UDT(MDT_String).

Module StringSet := MSetWeakList.Make StringAsDT.
Module StringSetFacts := WFactsOn StringAsDT StringSet.
Module StringSetEqProps := EqProperties StringSet.

Module StringMap := FMapWeakList.Make StringAsDT.
Module StringMapFacts := WFacts_fun StringAsDT StringMap.


(*
Module Type SYMBOL.
  Parameter terminal nonterminal : Type.

  Axiom t_eq_dec : 
    forall (x x2 : terminal),
      {x = x2} + {~x = x2}.

  Axiom nt_eq_dec : 
    forall (x x2 : nonterminal),
      {x = x2} + {~x = x2}.
End SYMBOL.

Module GrammarDefs (S : SYMBOL).

  Inductive symbol :=
  | T  : S.terminal -> symbol
  | NT : S.nonterminal -> symbol.

  Definition production := (S.nonterminal * list symbol)%type.

(* sets and maps of terminals *)
  Module MDT_T.
    Definition t := S.terminal.
    Definition eq_dec := S.t_eq_dec.
  End MDT_T.

  Module TasDT := Make_UDT(MDT_T).
  Module TSet := MSetWeakList.Make TasDT.
  Module TSetFacts := WFactsOn TasDT TSet.
  Module TSetEqProps := EqProperties TSet.

  Module TMap := FMapWeakList.Make TasDT.
  Module TMapFacts := WFacts_fun TasDT TMap.

  (* sets and maps of nonterminals *)
  Module MDT_NT.
    Definition t := S.nonterminal.
    Definition eq_dec := S.nt_eq_dec.
  End MDT_NT.

  Module NTasDT := Make_UDT(MDT_NT).
  Module NTSet := MSetWeakList.Make NTasDT.
  Module NTSetFacts := WFactsOn NTasDT NTSet.
  Module NTSetEqProps := EqProperties NTSet.

  Module NTMap := FMapWeakList.Make NTasDT.
  Module SymbolMapFacts := WFacts_fun NTasDT NTMap.

End GrammarDefs.

Module Type GRAMMAR (S : SYMBOL).

  Module GD := GrammarDefs(S).
  Parameter grammar : list GD.production.
  Parameter start   : S.nonterminal.

  Axiom startIn : 
    exists (p : GD.production),
      In p grammar /\ fst p = start.

End GRAMMAR.
      
Module StringSym <: SYMBOL.
  Definition nonterminal := string.
  Definition terminal := string.

  Lemma t_eq_dec : 
    forall (x x2 : terminal),
      {x = x2} + {~x = x2}.
  Proof. repeat decide equality. Defined.

  Lemma nt_eq_dec : 
    forall (x x2 : nonterminal),
      {x = x2} + {~x = x2}.
  Proof. repeat decide equality. Defined.
End StringSym.

Module Type STRING_GRAMMAR := GRAMMAR(StringSym).


Module MyGram <: STRING_GRAMMAR.
  Definition start := "hi".
  Definition grammar := [("hi", [GD.symbol.NT "there"; GD.symbol.T "sam"])].
End MyGram.

Definition grammar := (list production)%type.  
  

(* Create a module for sets of grammar symbols
   and a module for maps with grammar symbol keys *)

Definition symbol_eq_dec : forall (sy sy2 : symbol),
    {sy = sy2} + {~sy = sy2}.
Proof.
  intros. decide equality; apply String.string_dec.
Defined.

Module MDT_Symbol.
  Definition t := symbol.
  Definition eq_dec := symbol_eq_dec.
End MDT_Symbol.

Module SymbolAsDT := Make_UDT(MDT_Symbol).

Module SymbolSet := MSetWeakList.Make SymbolAsDT.
Module SymbolSetFacts := WFactsOn SymbolAsDT SymbolSet.
Module SymbolSetEqProps := EqProperties SymbolSet.

Module SymbolMap := FMapWeakList.Make SymbolAsDT.
Module SymbolMapFacts := WFacts_fun SymbolAsDT SymbolMap.

Inductive lookahead :=
| LA : string -> lookahead
| EOF : lookahead.

Definition lookahead_eq_dec : forall (la la2 : lookahead),
    {la = la2} + {~la = la2}.
Proof.
repeat decide equality. 
Defined.

Module Type GRAMMAR.
  Parameter terminal nonterminal : Set.

  Axiom t_eq_dec : forall (t t2 : terminal),
      {t = t2} + {~t = t2}.

  Axiom nt_eq_dec : forall (nt nt2 : nonterminal),
      {nt = nt2} + {~nt = nt2}.

  Definition 

Module Type ALPHABET
  Parameter terminal nonterminal : Set.

  Axiom t_eq_dec : forall (t t2 : terminal),
      {t = t2} + {~t = t2}.

  Axiom nt_eq_dec : forall (nt nt2 : nonterminal),
      {nt = nt2} + {~nt = nt2}.
End ALPHABET.

Module Alph <: ALPHABET.
  Definition terminal := string.
  Definition nonterminal := string.

  Lemma t_eq_dec : forall (t t2 : terminal),
      {t = t2} + {~t = t2}.
  Proof. repeat decide equality. Defined.

  Lemma nt_eq_dec : forall (nt nt2 : nonterminal),
      {nt = nt2} + {~nt = nt2}.
  Proof. repeat decide equality. Defined.
End Alph.

Module Type SYMBOL.

Module Symbol (A : ALPHABET).

  Inductive symbol :=
  | T  : A.terminal -> symbol
  | NT : A.nonterminal -> symbol.

  Definition isT sym :=
    match sym with 
    | T _ => true
    | NT _ => false
    end.

  Definition isNT sym := negb (isT sym).

End Symbol.

Module Production (S : Symbol).
  Module Symbol := Symbol(A).
  Definition production := (A.nonterminal * list Symbol.symbol)%type.

Module GrammarTypes (A : ALPHABET).
  Module Symbol := Symbol(A).
  Module 

  

  Parameter start : A.nonterminal.

  Definition production := (A.nonterminal * list symbol)%type.

  Parameter productions : list production.

End GRAMMAR.

Module StrGrammar <: GRAMMAR(Alph).
   Definition start := "hi".
   Definition productions := [("hi", [NT "there"; T "sam"])].
End StrGrammar.
  Inductive symbol :=
  | T : A.terminal -> symbol
  | NT : A.nonterminal -> symbol.
  
  Definition production := (A.nonterminal * list symbol)%type.


  Inductive symbol :=
  | 


  End Alph.

  Definition production := (nonterminal * list symbol)%type.

End GRAMMAR.

Module G <: GRAMMAR.

  Definition terminal := string.
  Definition nonterminal := string.

  Definition start := "hi".

  Inductive symbol :=
  | T : terminal -> symbol
  | NT : nonterminal -> symbol.

  Lemma t_eq_dec : forall (t t2 : terminal),
      {t = t2} + {~t = t2}.
  Proof. repeat decide equality. Defined.

End G.
*)