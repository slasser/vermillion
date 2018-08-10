Require Import List.

Require Import Lib.ExampleGrammars.
Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Import ListNotations.

Definition fromPairs (ps : list (ParseTable.key * list symbol)) : parse_table :=
  fold_right (fun p tbl =>
                match p with
                | (k, v) => ParseTable.add k v tbl
                end) (ParseTable.empty (list symbol)) ps.

(* Grammar 3.11 parse table definitions *)

Definition g311Pairs :=
  [ ((X, LA "if"),    [T "if"; NT E; T "then"; NT X; T "else"; NT X]);
    ((X, LA "begin"), [T "begin"; NT X; NT L]);
    ((X, LA "print"), [T "print"; NT E]);
       
    ((L, LA "end"),   [T "end"]);
    ((L, LA ";"),     [T ";"; NT X; NT L]);

    ((E, LA "num"),   [T "num"; T "=="; T "num"]) ].

Definition g311ParseTable := fromPairs g311Pairs.

(* xy_grammar parse table definitions *)

Definition xy_grammar_pairs :=
  [ ((X, EOF), [NT Y]);
    ((Y, EOF), []) ].

Definition xy_parse_table := fromPairs xy_grammar_pairs.

