Require Import List MSets String.
Require Import Lib.Derivation Grammar ParseTable Lib.Utils.
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
           
         | |- ?X = ?X => auto

         | |- isNT (NT _) = true => auto

         | |- isT (T _) = true => auto

         | |- nullable_gamma [] => constructor

         | |- first_sym (LA ?x) (T ?x) =>
           constructor

         | |- first_sym (LA _) (NT _) =>
           econstructor

         | |- first_gamma (LA ?x) (T ?x :: _) =>
           constructor

         (* contradictions *)
                                            
         | H : [] = (_ ++ _ :: _)%list |- _ =>
           apply app_cons_not_nil in H
                                       
         | H : false = true |- _ => inv H
                                        
         | H : False |- _ => inv H

         | H : isNT (T _) = true |- _ => inv H

         | H : isT (NT _) = true |- _ => inv H

         | H : first_gamma _ [] |- _ =>
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

         | H : first_prod _ _ [] |- _ =>
           inv H

         | H : isNT ?x = true, H2 : ?x = T _ |- _ =>
           subst

         | H : nullable_sym (T _) |- _ =>
           inv H

         | H : In _ [] |- _ => inv H

         (* unpacking assumptions *)

         | H : (_ :: _) = (_ :: _) |- _ =>
           inv H

         | H : pair (String _ _) _ = pair _  _ |- _ =>
           inv H

         | H : first_sym ?NT ?T |- SymbolSet.In ?T _ =>
           inv H

         | H : StringMap.Raw.PX.MapsTo _ _ _ |- _ =>
           inv H

         | H : StringMap.Raw.PX.eqke _ _ |- _ =>
           inv H

         | H : fst _ = fst _ |- _ =>
           simpl in H; subst

         | H : snd _ = snd _ |- _ =>
           simpl in H; subst

         | H : SymbolMap.find (NT (String _ _)) _ = Some _
           |- _ => inv H

         | H : first_gamma ?la (_::_) |-
           SymbolMap.find ?la _ = Some _ =>
           inv H

         | H : first_gamma ?la (_::_) |-
           LookaheadSet.In ?la _  =>
           inv H

         | H : In (_, _) _ |- _ =>
           inv H

         | H : SymbolSet.In _ _ |- _ => inv H

         | H : InA _ _ (_::_) |- _ => inv H

         | H : _ = SymbolSet.this _ |- _ => inv H

         | H : first_prod _ _  _ |- _ =>
           inv H

         | H : first_gamma _ (T _ :: _) |- _ =>
           inv H

         | H : first_gamma (LA _) (NT _ :: _) |- _ =>
           inv H
                                                
         | H : first_sym _ (T (String _ _)) |- _ =>
           inv H

         | H : first_sym _ (NT (String _ _)) |- _ =>
           inv H

         | H : (_::_) = ([] ++ _ :: _)%list |- _ =>
           inv H

         | H : (_::_) = ((_ :: _) ++ _ :: _)%list |- _ =>
           inv H
               
         | H : (_::_) = (?pre ++ _ :: _)%list |- _ =>
           destruct pre

         | H : nullable_prod _ _ |- _ =>
           inv H

         | H : nullable_gamma (_::_) |- _ =>
           inv H

         | H : follow_sym ?y (NT _) |- SymbolSet.In ?y _ =>
           inv H

         | H : NT _ = NT (String _ _) |- _ => inv H

         (* lists, maps, and sets *)
                  
         | |- SymbolMap.find _ _ = Some _ =>
           unfold StringMap.find; auto
                                    
         | |- In _ _ =>
           repeat (try (left; reflexivity); right)

         | |- SymbolSet.In (NT (String _ _)) _ =>
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)

         | |- LookaheadSet.In _ _ =>
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)

         (* simplifying goals *)

         | |- _ /\ _ => split
                  
         | |- StringMap.find _ _ = Some _  /\
              SymbolSet.In _ _ =>
           split

         | |- SymbolMap.find _ _ = Some _  /\
              SymbolMap.find _ _ = Some _ =>
           split

         | |- nullable_prod (NT (String _ _)) _ => constructor

         | |- nullable_sym (NT (String _ _)) => econstructor

         | |- nullable_gamma (_ :: _) => constructor

         | |- first_prod _ _ _ => apply FiProd

         | |- first_gamma ?X (String _ _) (T ?X :: _) =>
           apply FiGammaHd

         end.
