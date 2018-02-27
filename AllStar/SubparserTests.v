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

Example Z_abc : 
  adaptivePredict g312 "Z" ["a"; "b"; "c"] nil =
  Choice [NT "X"; NT "Y"; NT "Z"].
Proof. compute. Abort.

Example Z_ababd :
  adaptivePredict g312 "Z" ["a"; "b"; "a"; "b"; "d"] nil = 
  Choice [NT "X"; NT "Y"; NT "Z"].
Proof. compute. Abort.

Example X_a : 
  exists sps, adaptivePredict g312 "X" ["a"] nil =
              Conflict sps.
Proof. 
  eexists. compute. Abort.

(* Should this really be an unambiguous choice, 
   or should we report a conflict,
   or reject the grammar altogether? *)
Example Z_d : 
  adaptivePredict g312 "Z" ["d"] nil = Choice [].
Proof. compute. Abort.

