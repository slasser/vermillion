Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Import ListNotations.

Definition pt_entry := (nonterminal * lookahead * list symbol)%type.

Lemma pt_entry_dec :
  forall p p2 : pt_entry,
    {p = p2} + {p <> p2}.
Proof.
  repeat decide equality.
Defined.

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Fixpoint firstLookahead (nu : NtSet.t) (fi : nt_ls_map) (gamma : list symbol) :
  list lookahead :=
  match gamma with 
  | [] => []
  | T y :: _ => [LA y]
  | NT x :: gamma' => 
    let xFirst := match NtMap.find x fi with
                  | Some s => LaSet.elements s
                  | None => []
                  end
    in  if NtSet.mem x nu then xFirst ++ firstLookahead nu fi gamma' else xFirst
  end.

Fixpoint nullableGamma (nu : NtSet.t) (gamma : list symbol) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma nu gamma' else false
  end.

Definition followLookahead nu fo x gamma :=
  if nullableGamma nu gamma then
    match NtMap.find x fo with 
    | Some s => LaSet.elements s
    | None => []
    end
  else 
    [].

Definition fromLookaheadList x gamma las : list pt_entry :=
  map (fun la => (x, la, gamma)) las.

Definition mkEntriesForProd nu fi fo (prod : production) : list pt_entry :=
  let (x, gamma) := prod in
  let fil := firstLookahead nu fi gamma in
  let fol := followLookahead nu fo x gamma in
  fromLookaheadList x gamma (fil ++ fol).

Definition mkParseTableEntries nu fi fo g :=
  flat_map (mkEntriesForProd nu fi fo) g.(productions).

(* Build a parse table from a (correct) list of parse table entries *)

Definition empty_pt := ParseTable.empty (list symbol).

Definition addEntry (p : pt_entry) (o : option parse_table) :=
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

Definition mkParseTable (ps : list pt_entry) :=
  fold_right addEntry (Some empty_pt) ps.

