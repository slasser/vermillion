Require Import FMaps.
Require Import MSets.
Require Import String.

Inductive symbol :=
| EPS : symbol
| T   : string -> symbol
| NT  : string -> symbol.

Definition production := (symbol * list symbol)%type.
Definition lhs (p : production) := fst p.
Definition rhs (p : production) := snd p.

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

Module SymbolMap := FMapWeakList.Make SymbolAsDT.
Module SymbolMapFacts := WFacts_fun SymbolAsDT SymbolMap.