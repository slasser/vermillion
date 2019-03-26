Require Import List String.
Require Import FMaps MSets.
Import ListNotations.

Definition terminal := string.
Definition nonterminal := nat.

Inductive symbol :=
  | T  : terminal -> symbol
  | NT : nonterminal -> symbol.

Definition symbol_eq_dec : forall (sy sy2 : symbol),
    {sy = sy2} + {~sy = sy2}.
Proof.
  intros; repeat decide equality.
Defined.

Definition production := (nonterminal * list symbol)%type.

Record grammar := { productions : list production;
                    start : nonterminal }.

Module NT_as_DT <: UsualDecidableType := Nat_as_OT.

Module NtSet := MSetWeakList.Make NT_as_DT.
Module NtSetFacts := WFactsOn NT_as_DT NtSet.
Module NtSetEqProps := EqProperties NtSet.

Module NtMap := FMapWeakList.Make NT_as_DT.
Module NtMapFacts := WFacts_fun NT_as_DT NtMap.

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

