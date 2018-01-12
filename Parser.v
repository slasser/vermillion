Require Import Grammar.
Require Import ParseTable.
Require Import ParseTree.
Require Import String.
Require Import ListSet.
Require Import MSets.
Require Import FMaps.
Require Import List.
Require Import ParserUtils.
Import ListNotations.
Open Scope string_scope.


Definition mkNullableSet g fuel :=
  let updateNu (prod : production) nSet :=
      let (x, ys) := prod in
      if forallb (nullable nSet) ys then SymbolSet.add x nSet else nSet
  in  fixp (fun nu => fold_right updateNu nu g) SymbolSet.equal SymbolSet.empty fuel.


Definition mkFirstSet g nu fuel :=
  let fix updateFi (prod : production) fi :=
      let (x, ys) := prod in
      let fix helper x ys fi :=
          match ys with
          | nil => fi
          | EPS :: ys'  => helper x ys' fi
          | T s :: ys'  => SymbolMap.add x (SymbolSet.add (T s) (getOrEmpty x fi)) fi 
          | NT s :: ys' =>
            let vx := SymbolSet.union (getOrEmpty x fi) (getOrEmpty (NT s) fi) in
            let fi' := SymbolMap.add x vx fi in
            if SymbolSet.mem (NT s) nu then helper x ys' fi' else fi'
          end
      in  helper x ys fi
  in  fixp (fun fi => fold_right updateFi fi g)
           (SymbolMap.equal SymbolSet.equal)
           (SymbolMap.empty SymbolSet.t)
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
                  | nil => SymbolMap.add (NT s) (SymbolSet.union (getOrEmpty x fo) (getOrEmpty (NT s) fo)) fo
                  | z :: zs =>
                    let fo' := SymbolMap.add (NT s) (SymbolSet.union (getOrEmpty (NT s) fo) (getOrEmpty z fi)) fo in
                    if nullable nu z then loopr zs fo' else fo'
                  end
              in  helper x ys' (loopr ys' fo)
            | _ :: ys' => helper x ys' fo
            end
        in  helper x ys fo
      end            
  in  fixp (fun fo => fold_right updateFo fo g) (SymbolMap.equal SymbolSet.equal) (SymbolMap.empty SymbolSet.t) fuel.


Record nff := mkNFF {nu : SymbolSet.t;
                     fi : SymbolMap.t SymbolSet.t;
                     fo : SymbolMap.t SymbolSet.t}.

Definition gToNFF g fuel :=
  let nu := mkNullableSet g fuel in
  let fi := mkFirstSet g nu fuel in
  let fo := mkFollowSet g nu fi fuel in
  mkNFF nu fi fo.


Fixpoint firstGamma gamma nu fi :=
  match gamma with
  | nil => SymbolSet.empty
  | y :: ys =>
    if nullable nu y then
      SymbolSet.union (first fi y) (firstGamma ys nu fi)
    else
      first fi y
  end.

Definition nullableGamma ys nu := forallb (nullable nu) ys.

Definition mkParseTable g fuel :=
  let nff := gToNFF g fuel in
  let addEntry entry nt t ma :=
      let row :=  match SymbolMap.find nt ma with
                  | Some r => r
                  | None   => (SymbolMap.empty (list production))
                  end  in
      let cell := match SymbolMap.find t row with
                  | Some c => c
                  | None   => nil
                  end  in
      SymbolMap.add nt (SymbolMap.add t (entry :: cell) row) ma  in
  let addProd prod tbl :=
      match prod with
        | (x, ys) =>
          let fg := firstGamma ys (nu nff) (fi nff) in
          let ts := if nullableGamma ys (nu nff) then
                      SymbolSet.union fg (getOrEmpty x (fo nff))
                    else
                      fg
          in  SymbolSet.fold (addEntry (x, ys) x) ts tbl
      end
  in  fold_right addProd (SymbolMap.empty (SymbolMap.t (list production))) g.

Fixpoint parseLoop (pt : SymbolMap.t (SymbolMap.t (list production)))
         (stack : list symbol)
         (input : list string) (fuel : nat) : bool :=
  match fuel with
  | O   => false
  | S n =>
    match (stack, input) with
    | (nil, _) => true
    | (NT ntName :: stack', token :: _) =>
      match parseTableLookup (NT ntName) (T token) pt with
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

Definition parse pt start input fuel :=
  parseLoop pt [start] input fuel.