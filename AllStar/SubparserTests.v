Require Import List String.
Require Import ExampleGrammars Grammar Subparser Lib.Utils.
Import ListNotations.
Require Import Grammar.

(* Grammar 3.12 *)
(*
[(NT "Z", [T "d"]); 
 (NT "Z", [NT "X"; NT "Y"; NT "Z"]); 
 (NT "Y", []); 
 (NT "Y", [T "c"]); 
 (NT "X", [NT "Y"]); 
 (NT "X", [T "a"])]
 *)

(* spClosure works with an empty stack *)
Example spClosureTest1 :
  spClosure g312 (nonterminals (productions g312)) {| stack := nil; pred := [T "d"] |} =
  [{| stack := nil; pred := [T "d"] |}].
Proof.
  unfold spClosure. simpl. reflexivity.
Qed.

(* it also works when the top stack element is a terminal *)
Example spClosureTest2 :
  spClosure g312 (nonterminals (productions g312)) {| stack := [T "d"]; pred := [T "d"] |} =
  [{| stack := [T "d"]; pred := [T "d"] |}].
Proof.
  unfold spClosure. simpl. reflexivity.
Qed.

(* nonterminal that doesn't appear in Grammar 3.12 *)
Definition out_of_vocab := 42. 

Example spClosureTest3 :
  spClosure g312 (nonterminals (productions g312)) {| stack := [NT out_of_vocab]; pred := [T "d"] |} = nil.
Proof.
  unfold spClosure. simpl. reflexivity.
Qed.

Example spClosureTest4 :
  spClosure g312
            (nonterminals (productions g312))
            {| stack := [NT X; NT Y; NT Z];
               pred := [NT X; NT Y; NT Z] |} =
  [{|
      stack := [T "c"; NT Y; NT Z];
      pred := [NT X; NT Y; NT Z]
   |};
   {|
     stack := [T "a"; NT Y; NT Z];
     pred := [NT X; NT Y; NT Z]
   |}].
Proof. compute. reflexivity. Qed.

Example Z_abc : 
  adaptivePredict g312 Z ["a"; "b"; "c"] nil =
  Choice [NT X; NT Y; NT Z].
Proof. compute. reflexivity. Qed. 

Example Z_ababd :
  adaptivePredict g312 Z ["a"; "b"; "a"; "b"; "d"] nil = 
  Choice [NT X; NT Y; NT Z].
Proof. compute. reflexivity. Qed.

Example X_a : 
  exists sps, adaptivePredict g312 X ["a"] nil =
              Conflict sps.
Proof. eexists. compute. reflexivity. Qed.

(* Should this really be an unambiguous choice, 
   or should we report a conflict,
   or reject the grammar altogether? *)
Example Z_d : 
  adaptivePredict g312 Z ["d"] nil = Choice [].
Proof. compute. Abort.

