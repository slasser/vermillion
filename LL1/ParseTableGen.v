Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Definition prod_la_pair := (production * lookahead)%type.

Lemma prod_la_pair_dec :
  forall p p2 : prod_la_pair,
    {p = p2} + {p <> p2}.
Proof.
  repeat decide equality.
Defined.

Definition empty_pt := ParseTable.empty (list symbol).

Definition addEntry (p : prod_la_pair) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | ((x, gamma), la) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition mkParseTable (ps : list prod_la_pair) :=
  fold_right addEntry (Some empty_pt) ps.

