Require Import Grammar.
Require Import List.
Import ListNotations.

(* Grammar 3.11 from Appel's "Modern Compiler Implementation in ML" *)
Definition g311 : grammar :=
  [
    (NT "S", [T "if"; NT "E"; T "then"; NT "S"; T "else"; NT "S"]);
   (NT "S", [T "begin"; NT "S"; NT "L"]);
   (NT "S", [T "print"; NT "E"]);
  
   (NT "L", [T "end"]);
   (NT "L", [T ";"; NT "S"; NT "L"]);
   
   (NT "E", [T "num"; T "=="; T "num"])].

(* Grammar 3.12 from Appel's "Modern Compiler Implementation in ML" *)
Definition g312 : grammar :=
  [(NT "Z", [T "d"]); 
   (NT "Z", [NT "X"; NT "Y"; NT "Z"]);
   (NT "Y", []);
   (NT "Y", [T "c"]);
   (NT "X", [NT "Y"]);
   (NT "X", [T "a"])].