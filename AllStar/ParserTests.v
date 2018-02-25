Require Import String List.
Require Import AllStar.Parser ExampleGrammars
               Grammar Subparser Lib.Utils.
Import ListNotations.

Print g311.
(*
[(NT "S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]);
 (NT "S", [T "begin"; NT "S"; NT "L"]);
 (NT "S", [T "print"; NT "E"]); (NT "L", [T "end"]);
 (NT "L", [T ";"; NT "S"; NT "L"]);
 (NT "E", [T "num"; T "=="; T "num"])]
*)

Definition prog1 :=
  tokenize "if num == num then print num == num else print num == num".

Example test1 :
    parse g311 (NT "S") prog1 100 = (Some g311ParseTree1, nil).
Proof. reflexivity. Qed.

Definition prog2 := tokenize "begin print num == num end".

Example test2 :
  exists tr suf,
    parse g311 (NT "S") prog2 100 = (Some tr, suf).
Proof. compute. repeat eexists. Qed.

Definition prog3 :=
  tokenize "begin print num == num ; print num == num end".

Example test3 :
  exists tr suf,
    parse g311 (NT "S") prog3 100 = (Some tr, suf).
Proof. compute. repeat eexists. Qed.
           