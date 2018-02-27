Require Import String List.
Require Import AllStar.Parser ExampleGrammars
               Grammar Subparser Lib.Utils.
Import ListNotations.

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

Definition testProgram := prog3.

(* This is a simple demo of adaptivePredict's behavior.

   Here's a grammar for a simple programming language: *)
Compute g311.
(*
[(NT "S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]);
 (NT "S", [T "begin"; NT "S"; NT "L"]);
 (NT "S", [T "print"; NT "E"]); (NT "L", [T "end"]);
 (NT "L", [T ";"; NT "S"; NT "L"]);
 (NT "E", [T "num"; T "=="; T "num"])]
 *)

(* And here's a simple program that the grammar 
   should recognize: *)
Compute testProgram.

(* The first thing that adaptivePredict does is call 
   startState, which compute the initial DFA state for 
   prediction. *)
Definition dfaState0 := startState g311 "S" nil.
Compute dfaState0.

(* Next, the target function advances all of the subparsers 
   by one step. *)
Definition dfaState1 := target g311 dfaState0 "begin".
Compute dfaState1.

Definition dfaState2 := target g311 dfaState1 "print".
Compute dfaState2.

(* At this point, there's only one subparser, so
   adaptivePredict should return the prediction associated 
   with that subparser. The adaptivePredict call below shows 
   that that's what it does. *)
Compute adaptivePredict g311 "S" testProgram nil.

