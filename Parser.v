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

Inductive stack_elt :=
| Sym : symbol -> stack_elt
| Sep : string -> nat -> stack_elt.

Print List.

Inductive parse_result {A} :=
| Accept     : (@parse_tree A) -> parse_result
| Reject     : string -> parse_result
| OutOfFuel  : parse_result
| ParserBug  : string -> parse_result.

Fixpoint parseLoop
         (tbl       : parse_table)
         (gramStack : list stack_elt)
         (semStack  : list parse_tree)
         (input     : list string)
         (fuel      : nat) : parse_result :=
  match fuel with
  | O   => OutOfFuel
  | S n =>
    match (gramStack, input) with
    | (nil, _) =>
      match semStack with
      | [tree] => Accept tree
      | _      => ParserBug "non-singleton sem stack"
      end
    | (Sym (NT x) :: stack', token :: _) =>
      match parseTableLookup (NT x) (T token) tbl with
      | None    => Reject "parse table lookup failed"
      | Some ys =>
        let syms := map Sym ys in
        let sep  := Sep x (length ys) in
        parseLoop tbl (syms ++ sep :: stack') semStack input n
      end
    | (Sym (T y) :: stack', token :: input') =>
      match cmpSymbol (T y) (T token) with
      | true  => parseLoop tbl stack' (Leaf y :: semStack) input' n
      | false => Reject "token mismatch"
      end
    | (Sym _ :: _, nil) => Reject "no lookahead"
    | (Sep x len :: stack', _) =>
      let subtree := Node x (rev (firstn len semStack)) in
      let semStack' := subtree :: (skipn len semStack)  in
      parseLoop tbl stack' semStack' input n
    end
  end.

Definition parse tbl start input fuel :=
  parseLoop tbl [Sym (NT start)] nil input fuel.



Fixpoint mkTree (tbl : parse_table)
                (sym : symbol)
                (input : list string)
                (fuel : nat) :
                (option (parse_tree) * list string) :=
  match fuel with
  | O => (None, input)
  | S n =>
    match (sym, input) with
    | (T y, token :: input') =>
      if cmpSymbol (T y) (T token) then
        (Some (Leaf y), input')
      else
        (None, input)
    | (NT x, token :: _) =>
      match parseTableLookup sym (T token) tbl with
      | Some gamma =>
        let (sub, input') := mkSubtrees tbl gamma input [] n in
        match sub with
        | Some subtrees => (Some (Node x subtrees), input')
        | None          => (None, input')
        end
      | None => (None, input)
      end
    | (_, nil) => (None, nil)
    end
  end
with mkSubtrees (tbl : parse_table)
                (gamma : list symbol)
                (input : list string)
                (subtrees : list parse_tree)
                (fuel : nat) :
       (option (list parse_tree) * list string) :=
       match fuel with
       | O => (None, input)
       | S n => 
         match gamma with
         | nil => (Some (rev subtrees), input)
         | sym :: gamma' =>
           let (sub, input') := mkTree tbl sym input n in
           match sub with
           | Some st =>
             mkSubtrees tbl gamma' input' (st :: subtrees) n
           | None => (None, input')
           end
         end
       end.