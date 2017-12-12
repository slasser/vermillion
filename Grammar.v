Require Import List.
Require Import Parser.
Require Import String.
Import ListNotations.

Definition gSimple : grammar :=
  [(NT "A", [T "a"; T "b"]);
   (NT "X", [T "x"; T "y"])].

Definition g311 : grammar :=
  [(NT "S", [T "if" ; NT "E" ; T "then" ; NT "S" ; T "else" ; NT "S"]) ;
   (NT "S", [T "begin" ; NT "S" ; NT "L"]) ;
   (NT "S", [T "print" ; NT "E"]) ;
  
   (NT "L", [T "end"]) ;
   (NT "L", [T ";" ; NT "S" ; NT "L"]) ;
   
   (NT "E", [T "num" ; T "==" ; T "num"])].