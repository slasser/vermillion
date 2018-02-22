Require Import List String.
Require Import ExampleGrammars Grammar Subparser.
Import ListNotations.


Print g312.
(*
[(NT "Z", [T "d"]); 
 (NT "Z", [NT "X"; NT "Y"; NT "Z"]); 
 (NT "Y", []); 
 (NT "Y", [T "c"]); 
 (NT "X", [NT "Y"]); 
 (NT "X", [T "a"])]
*)

Compute adaptivePredict g312 "Z" ["a"; "b"; "c"].

Compute adaptivePredict g312 "X" ["a"].

Definition ss := startState g312 "X" ["a"].
Definition t1 := target g312 ss.
Definition t2 := target g312 t1.
Definition t3 := target g312 t2.

Compute ss.
(*
[{|
    busy := [];
    syms := [NT "Y"];
    input := ["a"];
    prediction := [NT "Y"];
    stack := [] |};
 {|
   busy := [];
   syms := [T "a"];
   input := ["a"];
   prediction := [T "a"];
   stack := [] |}]
 *)

Compute t1.
(*
[{|
    busy := [NT "Y"];
    syms := [];
    input := ["a"];
    prediction := [NT "Y"];
    stack := [[]] |};
 {|
   busy := [NT "Y"];
   syms := [T "c"];
   input := ["a"];
   prediction := [NT "Y"];
   stack := [[]] |};
 {|
   busy := [];
   syms := [];
   input := [];
   prediction := [T "a"];
   stack := [] |}]
*)

Compute t2.
(*
[{|
    busy := [NT "Y"];
    syms := [];
    input := ["a"];
    prediction := [NT "Y"];
    stack := [] |};
 {|
   busy := [];
   syms := [];
   input := [];
   prediction := [T "a"];
   stack := [] |}]
*)