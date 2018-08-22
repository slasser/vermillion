Require Import List.

Require Import Lib.Grammar.

Require Import LL1.ParseTable.

Import ListNotations.

(* Compute the NULLABLE set for a grammar *)

Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
  end.

Definition updateNu p acc:=
  match (p, acc) with
  | ((x, gamma), (candidates, nu)) =>
     if NtSet.mem x candidates && nullableGamma gamma nu then
       (NtSet.remove x candidates, NtSet.add x nu)
     else
       (candidates, nu)
     end.

Definition nullablePass ps acc :=
  fold_right updateNu acc ps.

(* Incomplete attempt to write mkNullableSet without fuel *)

Definition card_order (p1 p2 : NtSet.t * NtSet.t) := 
  let (candidates1, _) := p1 in 
  let (candidates2, _) := p2 in
  NtSet.cardinal candidates1 < NtSet.cardinal candidates2.

Lemma card_order_wf' : 
  forall n candidates nu, 
    NtSet.cardinal candidates <= n
    -> Acc card_order (candidates, nu).
Proof.
  induction n as [| n]; intros candidates1 nu1 Hle; constructor; 
  intros (candidates2, nu2) Hco; unfold card_order in Hco; try omega.
  apply IHn; omega.
Defined.

Lemma card_order_wf : well_founded card_order.
Proof.
  unfold well_founded; intros (candidates, nu).
  eapply card_order_wf'; eauto.
Defined.

Definition mkNullableSet (ps : list production) : (NtSet.t * NtSet.t) -> NtSet.t.
  refine (Fix card_order_wf
              (fun _ => _)
              (fun (pr : NtSet.t * NtSet.t) 
                   (mkNullableSet : forall pr', card_order pr' pr -> NtSet.t) =>
                 let (candidates, nu) := pr in
                 let (candidates', nu') := nullablePass ps pr in
                 if NtSet.eq_dec candidates candidates' then 
                   nu' 
                 else 
                   mkNullableSet (candidates', nu') _)).
Abort.

Definition ntSetFromList (ls : list nonterminal) :=
  fold_right NtSet.add NtSet.empty ls.

Definition lhSet (g : grammar) :=
  ntSetFromList (map fst (productions g)).

Fixpoint mkNullableSet' (ps : list production) 
                       (candidates nu : NtSet.t) 
                       (fuel : nat) :=
  match fuel with
  | O => None 
  | S n => 
    let (candidates', nu') := nullablePass ps (candidates, nu) in
    if NtSet.eq_dec candidates candidates' then
      Some nu'
    else
      mkNullableSet' ps candidates' nu' n
  end.

Definition mkNullableSet (g : grammar) (fuel : nat) :=
  mkNullableSet' (productions g) (lhSet g) NtSet.empty fuel.

Lemma mkNullableSet_sound :
  forall g fuel nu,
    mkNullableSet g fuel = Some nu
    -> nullable_set_for nu g.
Proof.
  intros g fuel nu Hmk.
  unfold mkNullableSet in Hmk.
Abort.

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition table_entry := (nonterminal * lookahead * list symbol)%type.

Lemma table_entry_dec :
  forall e e2 : table_entry,
    {e = e2} + {e <> e2}.
Proof.
  repeat decide equality.
Defined.

(* Build a list of parse table entries from (correct) NULLABLE, FIRST, and FOLLOW sets. *)

Definition fromLookaheadList x gamma las : list table_entry :=
  map (fun la => (x, la, gamma)) las.

Fixpoint firstGamma (gamma : list symbol) (nu : NtSet.t) (fi : first_map) :
  list lookahead :=
  match gamma with 
  | [] => []
  | T y :: _ => [LA y]
  | NT x :: gamma' => 
    let xFirst := match NtMap.find x fi with
                  | Some s => LaSet.elements s
                  | None => []
                  end
    in  if NtSet.mem x nu then xFirst ++ firstGamma gamma' nu fi else xFirst
  end.

Definition firstEntries x gamma nu fi :=
  fromLookaheadList x gamma (firstGamma gamma nu fi).

Fixpoint nullableGamma (gamma : list symbol) (nu : NtSet.t) : bool :=
  match gamma with 
  | [] => true
  | T _ :: _ => false
  | NT x :: gamma' => if NtSet.mem x nu then nullableGamma gamma' nu else false
  end.

Definition followLookahead x gamma nu fo :=
  if nullableGamma gamma nu then
    match NtMap.find x fo with 
    | Some s => LaSet.elements s
    | None => []
    end
  else 
    [].

Definition followEntries x gamma nu fo :=
  fromLookaheadList x gamma (followLookahead x gamma nu fo).

Definition entriesForProd nu fi fo (prod : production) : list table_entry :=
  let (x, gamma) := prod in
  firstEntries x gamma nu fi ++ followEntries x gamma nu fo.

Definition tableEntries' nu fi fo ps :=
  flat_map (entriesForProd nu fi fo) ps.

Definition tableEntries nu fi fo g :=
  tableEntries' nu fi fo g.(productions).

(* Build a parse table from a (correct) list of parse table entries *)

Definition empty_table := ParseTable.empty (list symbol).

Definition addEntry (p : table_entry) (o : option parse_table) :=
  match o with
  | None => None
  | Some tbl =>
    match p with
    | (x, la, gamma) =>
      match pt_lookup x la tbl with
      | None => Some (pt_add x la gamma tbl)
      | Some gamma' =>
        if list_eq_dec symbol_eq_dec gamma gamma' then Some tbl else None (* make separate function *)
      end
    end
  end.

Definition tableFromEntries (ps : list table_entry) : option parse_table :=
  fold_right addEntry (Some empty_table) ps.

(* Combining all of the steps into a single function *)
(* The type of this function will change as I add code for computing NULLABLE, etc. *)

Definition mkParseTable g nu fi fo :=
  let es := tableEntries nu fi fo g in
  tableFromEntries es.
  

