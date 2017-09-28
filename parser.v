Require Import String.
Require Import ListSet.
Require Import MSets.
Require Import FMaps.
Require Import List.

Open Scope string_scope.

Inductive symbol :=
  | EPS : symbol
  | T   : string -> symbol
  | NT  : string -> symbol.

Definition symbol_eq_dec : forall (sy sy2 : symbol),
    {sy = sy2} + {~sy = sy2}.
Proof.
  intros. decide equality; apply String.string_dec.
Defined.

(* Create a module for sets of grammar symbols
   and a module for maps with grammar symbol keys
   To do : figure out why the previous approach
   that skipped Make_UDT didn't work. *)

Module MDT_Symbol.
  Definition t := symbol.
  Definition eq_dec := symbol_eq_dec.
End MDT_Symbol.

Module SymbolAsDT := Make_UDT(MDT_Symbol).

Module S := MSetWeakList.Make SymbolAsDT.

Module M := FMapWeakList.Make SymbolAsDT.

Definition addList syms se := fold_right S.add se syms. 

Definition production := (symbol * list symbol)%type.
Check production.

Definition grammar := (list production)%type.

Definition G311 : grammar := (NT "S", T "if" :: NT "E" ::  T "then" :: NT "S" :: T "else" :: NT "S" :: nil) :: nil.

(*

	    (NT "S", [T "begin", NT "S", NT "L"]),
	    (NT "S", [T "print", NT "E"]),

	    (NT "L", [T "end"]),
	    (NT "L", [T ";", NT "S", NT "L"]),

	    (NT "E", [T "num", T "=", T "num"])].
*)

Fixpoint isT (sy : symbol) : bool :=
  match sy with
  | T _ => true
  | _   => false
  end.


Definition nonterminals (g : grammar) :=
  addList (map fst g) S.empty.

Definition terminals (g : grammar) : S.t  := 
  let tsPerProd := map (compose (filter isT) snd) g
  in  fold_right (fun ts se => addList ts se) 
		 S.empty 
		 tsPerProd.

Eval compute in terminals G311.

Definition nullable nSet sym :=
  match sym with
  | EPS  => true
  | T _  => false
  | NT _ => S.mem sym nSet
  end.

Definition first fi sym :=
  match sym with
  | EPS  => S.empty
  | T _  => S.singleton sym
  | NT _ => match M.find sym fi with
            | Some se => se
            | None    => S.empty
            end
  end.

(* Previously got "Anomaly : not a sort" error, 
   maybe because I hadn't added the fuel argument *)
Definition fixp {A} update (cmp : A -> A -> bool) x0 fuel :=
  let fix iter x fuel :=
      match fuel with
      | O => x
      | S n =>
        let x' := update x in 
        if cmp x x' then x' else iter x' n
      end
  in iter x0 fuel.

Definition getOrEmpty k m :=
  match M.find k m with
  | Some v => v
  | None   => S.empty
  end.

Definition mkNullableSet g fuel :=
  let updateNu (prod : production) nSet :=
      let (x, ys) := prod in
      if forallb (nullable nSet) ys then S.add x nSet else nSet
  in  fixp (fun nu => fold_right updateNu nu g) S.equal S.empty fuel.

Print String.

(* There must be a way to avoid doing this. *)
Definition cmpSymbol sy sy2 := if SymbolAsDT.eq_dec sy sy2 then true else false.

(* Known issues : the (M.equal cmpSymbol) application is failing because Coq can't figure out
   that the map key type is the same as the set element type (they're both grammar symbols). *)
Definition mkFirstSet g nu fuel :=
  let fix updateFi (prod : production) fi :=
      let (x, ys) := prod in
      let fix helper x ys fi :=
          match ys with
          | nil => fi
          | EPS :: ys'  => helper x ys' fi
          | T s :: ys'  => M.add x (S.add (T s) (getOrEmpty x fi)) fi 
          | NT s :: ys' => helper x ys' fi
          end
      in  helper x ys fi
  in  fixp (fun fi => fold_right updateFi fi g)
           (M.equal cmpSymbol)
           (M.empty S.t)
           fuel.

(* Known issues : the return type of the pattern match against the production can't be inferred. *)
Definition mkFollowSet g nu fi fuel :=
  let updateFo (prod : production) fo :=
      let (x, ys) := prod in
      let fix helper (x : symbol) (ys : list symbol) fo :=
          match ys with
          | nil => fo
          | NT s :: ys' =>
            let fix loopr ys' fo :=
                match ys' with
                | nil => M.add (NT s) (S.union (getOrEmpty x fo) (getOrEmpty (NT s) fo)) fo
                | z :: zs =>
                  let fo' := M.add (NT s) (S.union (getOrEmpty (NT s) fo) (getOrEmpty z fi)) fo in
                  if nullable nu z then loopr zs fo' else fo'
                end
            in  helper x ys' (loopr ys' fo)
          | _ :: ys' => helper x ys' fo
          end
      in  helper x ys fo
  in  fixp (fun fo => fold_right updateFo fo g) (M.equal cmpSymbol) (M.empty symbol) fuel.

