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

Definition fromLookaheadList x gamma las : list pt_entry :=
  map (fun la => (x, la, gamma)) las.

Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : nt_ls_map) :
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

Definition mkFirstEntries x gamma nu fi :=
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

Definition mkFollowEntries x gamma nu fo :=
  fromLookaheadList x gamma (followLookahead x gamma nu fo).

Definition mkEntriesForProd nu fi fo (prod : production) : list pt_entry :=
  let (x, gamma) := prod in
  mkFirstEntries x gamma nu fi ++ mkFollowEntries x gamma nu fo.

Definition mkParseTableEntries' nu fi fo ps :=
  flat_map (mkEntriesForProd nu fi fo) ps.

Definition mkParseTableEntries nu fi fo g :=
  mkParseTableEntries' nu fi fo g.(productions).

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

