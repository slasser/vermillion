Require Import Grammar.
Require Import List.
Import ListNotations.

Definition parse_table := SymbolMap.t (SymbolMap.t (list production)).

Definition parseTableLookup (nt : symbol)
                            (t : symbol)
                            (pt : parse_table) : option production :=
  match SymbolMap.find nt pt with
  | None    => None
  | Some ma => match SymbolMap.find t ma with
               | None                  => None
               | Some nil              => None
               | Some (p1 :: p2 :: ps) => None
               | Some [p]              =>
                 let (x, ys) := p in Some (x, ys)
               end
  end.