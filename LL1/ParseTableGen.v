Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Import ListNotations.

Definition table_entry := (nonterminal * lookahead * list symbol)%type.

Lemma table_entry_dec :
  forall e e2 : table_entry,
    {e = e2} + {e <> e2}.
Proof.
  repeat decide equality.
Defined.

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition fromLookaheadList x gamma las : list table_entry :=
  map (fun la => (x, la, gamma)) las.

Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :
  list lookahead :=
  match gamma with 
  | [] => []
  | T y :: _ => [LA y]
  | NT x :: gamma' => 
    let xFirst := match NtMap.find x fi with
                  | Some s => LaSet.elements s
                  | None => []
                  end
    in  if NtSet.mem x nu then xFirst ++ firstGamma gamma' nu fi else xFirst
  end.

Definition firstEntries x gamma nu fi :=
  fromLookaheadList x gamma (firstGamma gamma nu fi).

Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
  end.

Definition followLookahead x gamma nu fo :=
  if nullableGamma gamma nu then
    match NtMap.find x fo with 
    | Some s => LaSet.elements s
    | None => []
    end
  else 
    [].

Definition followEntries x gamma nu fo :=
  fromLookaheadList x gamma (followLookahead x gamma nu fo).

Definition entriesForProd nu fi fo (prod : production) : list table_entry :=
  let (x, gamma) := prod in
  firstEntries x gamma nu fi ++ followEntries x gamma nu fo.

Definition tableEntries' nu fi fo ps :=
  flat_map (entriesForProd nu fi fo) ps.

Definition tableEntries nu fi fo g :=
  tableEntries' nu fi fo g.(productions).

(* Build a parse table from a (correct) list of parse table entries *)

Definition empty_table := ParseTable.empty (list symbol).

Definition addEntry (p : table_entry) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | (x, la, gamma) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition tableFromEntries (ps : list table_entry) : option parse_table :=
  fold_right addEntry (Some empty_table) ps.

(* Combining all of the steps into a single function *)
(* The type of this function will change as I add code for computing NULLABLE, etc. *)

Definition mkParseTable g nu fi fo :=
  let es := tableEntries nu fi fo g in
  tableFromEntries es.
  

