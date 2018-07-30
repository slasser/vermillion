Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Definition singletonLaMap la gamma :=
  LaMap.add la gamma (LaMap.empty (list symbol)).
  
Definition addEntry (x : nonterminal) (la : lookahead) (gamma : list symbol) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl => 
    match NtMap.find x tbl with
    | None => Some (NtMap.add x (singletonLaMap la gamma) tbl)
    | Some m =>
      match LaMap.find la m with
      | None => Some (NtMap.add x (LaMap.add la gamma m) tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None
      end
    end
  end.

Definition addProductionEntries (prod_and_la_set : production * LaSet.t)
                                (o : option parse_table) :=
  match prod_and_la_set with
  | ((x, gamma), laSet) =>
    fold_right (fun la o => addEntry x la gamma o) o (LaSet.elements laSet)
  end.

Definition empty_pt := NtMap.empty (LaMap.t (list symbol)).

Definition mkParseTable (prods_and_la_sets : list (production * LaSet.t)) :=
  fold_right addProductionEntries (Some empty_pt) prods_and_la_sets.