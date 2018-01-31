Require Import Derivation.
Require Import Grammar.
Require Import List.
Require Import MSets.
Require Import ParserUtils.
Require Import ParseTable.
Require Import String.
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
         | |- derives (T _) _ _ => apply derivesT
         | |- derives2 (T _) _  => apply derivesT2
         | |- derivesList (T ?s :: _) _ _ =>
           let tName := s
           in  apply derivesCons with (prefix := [tName])
         | |- derivesList2 (T ?s :: _) _  =>
           let tName := s
           in  apply derivesCons2 with (prefix := [tName])
         | |- derivesList [] _ _ => apply derivesNil
         | |- derivesList2 [] _  => apply derivesNil2
         | |- ?P = ?P => reflexivity
         | |- _ => simpl in *
         end.

Ltac crush :=
  repeat match goal with
           
         | |- ?X = ?X => reflexivity

         | |- isNT (NT _) = true => reflexivity

         | |- isT (T _) = true => reflexivity

         | |- firstSym (T ?X) (T ?X) =>
           apply first_t

         (* contradictions *)
                                            
         | H : [] = (_ ++ _ :: _)%list |- _ =>
           apply app_cons_not_nil in H
                                       
         | H : false = true |- _ => inv H
                                        
         | H : False |- _ => inv H

         | H : isNT (T _) = true |- _ => inv H

         | H : isT (NT _) = true |- _ => inv H

         | H : firstGamma _ [] |- _ => inv H

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

         (* unpacking assumptions *)

         | H : (_ :: _) = (_ :: _) |- _ =>
           idtac "inv eq lists" ; inv H

         | H : pair (NT _) _ = pair _  _ |- _ =>
           idtac "inv eq pairs" ; inv H

         | H : firstSym ?NT ?T |- SymbolSet.In ?T _ =>
           idtac "firstSym |- SymbolSet.In";
           inv H

         | H : SymbolMap.Raw.PX.MapsTo _ _ _ |- _ =>
           inv H

         | H : SymbolMap.Raw.PX.eqke _ _ |- _ =>
           inv H

         | H : fst _ = fst _ |- _ =>
           simpl in H; subst

         | H : snd _ = snd _ |- _ =>
           simpl in H; subst

         | H : SymbolMap.find (NT (String _ _)) _ = Some _
           |- _ => inv H

         | H : firstGamma _ (_::_) |- _ =>
           idtac "inv firstGamma" ; inv H

         | H : In (_, _) _ |- _ =>
           idtac "inv pair in list" ; destruct H

         | H : SymbolSet.In _ _ |- _ => inv H

         | H : InA _ _ (_::_) |- _ => inv H

         | H : _ = SymbolSet.this _ |- _ => inv H

         | H : firstProd _ (NT (String _ _)) (_ :: _) |- _ =>
           inv H

         | H : firstSym _ (T (String _ _)) |- _ =>
           inv H

         | H : firstSym _ (NT (String _ _)) |- _ =>
           inv H
(*
         | H : (_::_) = (?prefix ++ _ :: _)%list |- _ =>
           destruct prefix

 *)

         | H : (_::_) = ([] ++ _ :: _)%list |- _ =>
           inv H

         | H : (_::_) = ((_ :: _) ++ _ :: _)%list |- _ =>
           inv H
               
         (* lists, maps, and sets *)
                  
         | |- SymbolMap.find _ _ = Some _ =>
           idtac "SymbolMap.find = Some";
           unfold SymbolMap.find; reflexivity
                                    
         | |- In _ _ =>
           idtac "List.In";
           repeat (try (left; reflexivity); right)

         | |- SymbolSet.In (T (String _ _)) _ =>
           idtac "SymbolSet.In T";
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)

         | |- SymbolSet.In (NT (String _ _)) _ =>
           idtac "SymbolSet.In NT";
           repeat (try (apply InA_cons_hd; reflexivity);
                   apply InA_cons_tl)

         (* simplifying goals *)
                  
         | |- SymbolMap.find _ _ = Some _  /\ SymbolSet.In _ _ =>
           split 

         end.