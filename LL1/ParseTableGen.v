Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Definition pt_entry := (nonterminal * lookahead * list symbol)%type.

Lemma pt_entry_dec :
  forall p p2 : pt_entry,
    {p = p2} + {p <> p2}.
Proof.
  repeat decide equality.
Defined.

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

