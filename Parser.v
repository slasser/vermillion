Require Import String.
Require Import ListSet.
Require Import MSets.
Require Import FMaps.
Require Import List.
Import ListNotations.
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

(* Will adding an annotation make the ascription transparent? *)
Module S := MSetWeakList.Make SymbolAsDT.

Module SyMod := S.
Print SyMod.

Module M := FMapWeakList.Make SymbolAsDT.

Definition addList syms se := fold_right S.add se syms. 

Definition production := (symbol * list symbol)%type.

Definition lhs (p : production) := fst p.
Definition rhs (p : production) := snd p.

Definition grammar := (list production)%type.

Definition G311 : grammar :=
  (NT "S", T "if" :: NT "E" ::  T "then" :: NT "S" :: T "else" :: NT "S" :: nil) ::
  (NT "S", T "begin" :: NT "S" :: NT "L" :: nil) ::
  (NT "S", T "print" :: NT "E" :: nil) ::
  
  (NT "L", T "end" :: nil) :: 
  (NT "L", T ";" :: NT "S" :: NT "L" :: nil) ::

  (NT "E", T "num" :: T "=" :: T "num" :: nil) :: nil.

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

(*
Definition get (k : symbol) m default :=
  match M.find k m with
  | Some v => v
  | None   => default
  end.
*)

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


(* There must be a way to avoid doing this. *)
Definition cmpSymbol sy sy2 := if SymbolAsDT.eq_dec sy sy2 then true else false.


Definition mkFirstSet g nu fuel :=
  let fix updateFi (prod : production) fi :=
      let (x, ys) := prod in
      let fix helper x ys fi :=
          match ys with
          | nil => fi
          | EPS :: ys'  => helper x ys' fi
          | T s :: ys'  => M.add x (S.add (T s) (getOrEmpty x fi)) fi 
          | NT s :: ys' =>
            let vx := S.union (getOrEmpty x fi) (getOrEmpty (NT s) fi) in
            let fi' := M.add x vx fi in
            if S.mem (NT s) nu then helper x ys' fi' else fi'
          end
      in  helper x ys fi
  in  fixp (fun fi => fold_right updateFi fi g)
           (M.equal S.equal)
           (M.empty S.t)
           fuel.


Definition mkFollowSet g nu fi fuel :=
  let updateFo (prod : production) fo :=
      match prod with
      | (x, ys) =>
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
      end            
  in  fixp (fun fo => fold_right updateFo fo g) (M.equal S.equal) (M.empty S.t) fuel.


Record nff := mkNFF {nu : S.t; fi : M.t S.t; fo : M.t S.t}.

Definition gToNFF g fuel :=
  let nu := mkNullableSet g fuel in
  let fi := mkFirstSet g nu fuel in
  let fo := mkFollowSet g nu fi fuel in
  mkNFF nu fi fo.


Fixpoint firstGamma gamma nu fi :=
  match gamma with
  | nil => S.empty
  | y :: ys =>
    if nullable nu y then
      S.union (first fi y) (firstGamma ys nu fi)
    else
      first fi y
  end.

Definition nullableGamma ys nu := forallb (nullable nu) ys.

Type "a" :: nil.

Definition mkParseTable g fuel :=
  let nff := gToNFF g fuel in
  let addEntry entry nt t ma :=
      let row :=  match M.find nt ma with
                  | Some r => r
                  | None   => (M.empty (list production))
                  end  in
      let cell := match M.find t row with
                  | Some c => c
                  | None   => nil
                  end  in
      M.add nt (M.add t (entry :: cell) row) ma  in
  let addProd prod tbl :=
      match prod with
        | (x, ys) =>
          let fg := firstGamma ys (nu nff) (fi nff) in
          let ts := if nullableGamma ys (nu nff) then
                      S.union fg (getOrEmpty x (fo nff))
                    else
                      fg
          in  S.fold (addEntry (x, ys) x) ts tbl
      end
  in  fold_right addProd (M.empty (M.t (list production))) g.

Eval compute in mkParseTable G311 100.
Type mkParseTable.


Inductive ast {A} :=
| Node : A -> list ast -> ast
| Leaf : A -> ast.

Definition getRoot (tree : ast) : symbol :=
  match tree with
  | Node ntName _ => NT ntName
  | Leaf tName    => T tName
  end.

Definition parse g start input fuel1 fuel2 :=
  let pt := mkParseTable g fuel1 in
  let fix loop sym input fuel :=
      match fuel with
      | O   => None
      | S n =>
        match (sym, input) with
        | (NT ntName, token :: _) =>
          match M.find sym pt with
          | None    => None  (* No parse table entries for the NT *)
          | Some ma => match M.find (T token) ma with
                       | None                  => None (* No expansions of NT that start with T *)
                       | Some nil              => None
                       | Some (p1 :: p2 :: ps) => None
                       | Some (p :: nil) =>
                         let (x, ys) := p in
                         let subresult :=
                             fold_left (fun subtrees_input y =>
                                          match subtrees_input with
                                          | None => None
                                          | Some (subtrees, input) =>
                                            match loop y input n with
                                            | None => None
                                            | Some (subtree, input') =>
                                              Some (app subtrees (subtree :: nil), input')
                                            end
                                          end) ys (Some (nil, input))
                         in  match subresult with
                             | None => None
                             | Some (subtrees, input') => Some (Node ntName subtrees, input')
                             end
                       end
          end
        | (NT _, nil) => None
        | (T tName, token :: tokens) => match cmpSymbol (T tName) (T token) with
                                        | true =>  Some (Leaf tName, tokens)
                                        | false => None
                                        end
        | (T _, nil) => None
        | (EPS, _)   => Some (Leaf "", input) (* Come back to this *)
        end
      end
  in  loop start input fuel2.

Definition ptLookup (nt : symbol) (t : symbol)
           (pt : M.t (M.t (list production))) : option production :=
  match M.find nt pt with
  | None    => None
  | Some ma => match M.find t ma with
               | None                  => None
               | Some nil              => None
               | Some (p1 :: p2 :: ps) => None
               | Some [p]              =>
                 let (x, ys) := p in Some (x, ys)
               end
  end.

Fixpoint parseLoop (pt : M.t (M.t (list production)))
         (stack : list symbol)
         (input : list string) (fuel : nat) : bool :=
  match fuel with
  | O   => false
  | S n =>
    match (stack, input) with
    | (nil, _) => true
    | (NT ntName :: stack', token :: _) =>
      match ptLookup (NT ntName) (T token) pt with
      | None => false
      | Some (x, ys) => parseLoop pt (app ys stack') input n
      end
    | (NT _ :: _, nil) => false
    | (T tName :: stack', token :: input') =>
      match cmpSymbol (T tName) (T token) with
      | true  => parseLoop pt stack' input' n
      | false => false
      end
    | (T _ :: _, nil) => false
    | (EPS :: stack', _)   => parseLoop pt stack' input n
    end
  end.

Definition parse' pt start input fuel :=
  parseLoop pt [start] input fuel.



(* Stack-based version *)
(* To do : move lookup routine into separate function *)
Definition parse'' (pt : M.t (M.t (list production))) start input fuel :=
  let fix loop stack input fuel :=
      match fuel with
      | O   => false
      | S n =>
        match (stack, input) with
        | (nil, _) => true
        | (NT ntName :: stack', token :: _) =>
          match M.find (NT ntName) pt with
          | None    => false  (* No parse table entries for the NT *)
          | Some ma => match M.find (T token) ma with
                       | None                  => false (* No expansions of NT that start with T *)
                       | Some nil              => false
                       | Some (p1 :: p2 :: ps) => false
                       | Some [p] =>
                         let (x, ys) := p
                         in  loop (app ys stack') input n
                       end
          end
        | (NT _ :: _, nil) => false
        | (T tName :: stack', token :: input') =>
          match cmpSymbol (T tName) (T token) with
          | true  => loop stack' input' n
          | false => false
          end
        | (T _ :: _, nil) => false
        | (EPS :: stack', _)   => loop stack' input n
        end
      end
  in  loop [start] input fuel.

Type parse'.
