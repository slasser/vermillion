Require Import List MSets String.
Require Import Derivation Grammar ParseTable Lib.Utils.
Import ListNotations.
Open Scope string_scope.

Ltac inv H := inversion H; clear H; subst.

(* Add this to crush *)
Ltac solveNotFalse := simpl; unfold not; intros; inversion H.

Ltac proveSymBinding :=
  match goal with
  | H : [?X] = (?prefix ++ ?Y :: ?suffix)%list |-
    ?Y = ?X =>
    destruct prefix; inv H
  end.

Ltac derCrush :=
  repeat match goal with
         | |- _ /\ _ => split
         | |- In _ _ => repeat (try (left ; reflexivity) ; right)
         | |- derivesTree (T _) _ _ => apply derivesT
         | |- derivesForest (T ?s :: _) _ _ =>
           let tName := s
           in  apply derivesCons with (prefix := [tName])
         | |- derivesForest [] _ _ => constructor
         | |- ?P = ?P => reflexivity
         | |- _ => simpl in *
         end.

Ltac crush :=
  repeat match goal with
           
         | |- ?X = ?X => reflexivity

         | |- isNT (NT _) = true => reflexivity

         | |- isT (T _) = true => reflexivity

         | |- firstSym ?X (T ?X) =>
           apply FiT

         | |- firstGamma (?x) (?x :: _) =>
           apply FiGammaHd

         (* contradictions *)
                                            
         | H : [] = (_ ++ _ :: _)%list |- _ =>
           apply app_cons_not_nil in H
                                       
         | H : false = true |- _ => inv H
                                        
         | H : False |- _ => inv H

         | H : isNT (T _) = true |- _ => inv H

         | H : isT (NT _) = true |- _ => inv H

         | H : firstGamma _ [] |- _ =>
           inv H

         | H : ?X <> ?X |- _ =>
           exfalso; apply H; reflexivity

         | H : InA _ _ [] |- _ => inv H

         | |- NT _ <> T _ =>
           let H := fresh "Hcontra" in
           unfold not; intro H; inv H

         | |- NT ?X <> NT ?Y =>
              let H := fresh "Hcontra" in
              unfold not; intro H; progress inv H

         | H : (isNT ?x = true), H2 : (isT ?x = true) |- _ =>
           destruct x

         | H : firstProd _ _ [] |- _ =>
           inv H

         | H : firstGamma _ _ [] |- _ =>
           inv H

         | H : isNT ?x = true, H2 : ?x = T _ |- _ =>
           subst

         | H : nullableSym (T _) |- _ =>
           inv H

         | H : In _ [] |- _ => inv H

         (* unpacking assumptions *)

         | H : (_ :: _) = (_ :: _) |- _ =>
           inv H

         | H : pair (String _ _) _ = pair _  _ |- _ =>
           inv H

         | H : firstSym ?NT ?T |- StringSet.In ?T _ =>
           inv H

         | H : StringMap.Raw.PX.MapsTo _ _ _ |- _ =>
           inv H

         | H : StringMap.Raw.PX.eqke _ _ |- _ =>
           inv H

         | H : fst _ = fst _ |- _ =>
           simpl in H; subst

         | H : snd _ = snd _ |- _ =>
           simpl in H; subst

         | H : StringMap.find (String _ _) _ = Some _
           |- _ => inv H

         | H : StringMap.find (String _ _) _ = Some _
           |- _ => inv H

         | H : firstGamma ?y (_::_) |-
           StringMap.find ?y _ = Some _ =>
           inv H

         | H : firstGamma ?y (_::_) |-
           StringSet.In ?y _  =>
           inv H

         | H : In (_, _) _ |- _ =>
           inv H

         | H : StringSet.In _ _ |- _ => inv H

         | H : InA _ _ (_::_) |- _ => inv H

         | H : _ = StringSet.this _ |- _ => inv H
(*
         | H : firstProd _ (NT (String _ _)) (_ :: _) |- _ =>
           inv H

         | H : firstProd' _ (NT (String _ _)) (_ :: _) |- _ =>
           inv H
 *)
         | H : firstProd _ _  _ |- _ =>
           inv H

         | H : firstGamma _ (String _ _) _ |- _ =>
           inv H
                                                
         | H : firstSym _ (T (String _ _)) |- _ =>
           inv H

         | H : firstSym _ (NT (String _ _)) |- _ =>
           inv H

         | H : (_::_) = ([] ++ _ :: _)%list |- _ =>
           inv H

         | H : (_::_) = ((_ :: _) ++ _ :: _)%list |- _ =>
           inv H
               
         | H : (_::_) = (?pre ++ _ :: _)%list |- _ =>
           destruct pre

         | H : nullableGamma (_::_) |- _ =>
           inv H

         | H : followSym ?y (NT _) |- StringSet.In ?y _ =>
           inv H
               
         (* lists, maps, and sets *)
                  
         | |- StringMap.find _ _ = Some _ =>
           unfold StringMap.find; reflexivity
                                    
         | |- In _ _ =>
           repeat (try (left; reflexivity); right)

         | |- StringSet.In (String _ _) _ =>
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)

         (* simplifying goals *)
                  
         | |- StringMap.find _ _ = Some _  /\
              StringSet.In _ _ =>
           split

         | |- StringMap.find _ _ = Some _  /\
              StringMap.find _ _ = Some _ =>
           split

         | |- nullableProd (String _ _) _ =>
           apply NuProd

         | |- firstProd _ _ _ =>
           apply FiProd

         | |- firstGamma ?X (String _ _) (T ?X :: _) =>
           apply FiGammaHd

         end.

