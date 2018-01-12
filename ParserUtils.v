Require Import Grammar.

Definition nullable nSet sym :=
  match sym with
  | EPS  => true
  | T _  => false
  | NT _ => SymbolSet.mem sym nSet
  end.

Definition first fi sym :=
  match sym with
  | EPS  => SymbolSet.empty
  | T _  => SymbolSet.singleton sym
  | NT _ => match SymbolMap.find sym fi with
            | Some se => se
            | None    => SymbolSet.empty
            end
  end.

Definition fixp {A} update (cmp : A -> A -> bool) x0 fuel :=
  let fix iter x fuel :=
      match fuel with
      | O => x
      | S n =>
        let x' := update x in 
        if cmp x x' then x' else iter x' n
      end
  in iter x0 fuel.

Definition getOrEmpty k m :=
  match SymbolMap.find k m with
  | Some v => v
  | None   => SymbolSet.empty
  end.

(* There must be a way to avoid doing this. *)
Definition cmpSymbol sy sy2 := if SymbolAsDT.eq_dec sy sy2 then true else false.