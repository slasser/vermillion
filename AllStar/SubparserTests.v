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
  adaptivePredict g312 "Z" ["a"; "b"; "c"] = Choice [NT "X"; NT "Y"; NT "Z"].
Proof. reflexivity. Qed.

Example Z_ababd :
  adaptivePredict g312 "Z" ["a"; "b"; "a"; "b"; "d"] = 
  Choice [NT "X"; NT "Y"; NT "Z"].
Proof. reflexivity. Qed.

Example X_a : 
  exists sps, adaptivePredict g312 "X" ["a"] = Conflict sps.
Proof. 
  eexists. reflexivity. Qed.

(* Should this really be an unambiguous choice, 
   or should we report a conflict,
   or reject the grammar altogether? *)
(* Wrong -- change back *)
Example Z_d : 
  adaptivePredict g312 "Z" ["d"] = Choice [].
Proof. compute. reflexivity. Qed.

