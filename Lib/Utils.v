Require Import Ascii List Omega String.
Require Import Grammar.
Import ListNotations.
Open Scope string_scope.

Definition isNT sym :=
  match sym with
  | NT _ => true
  | _    => false
  end.

Definition isT sym :=
  match sym with
  | T _ => true
  | _   => false
  end.

Definition nullable nSet sym :=
  match sym with
  | T _  => false
  | NT x => StringSet.mem x nSet
  end.

Definition first fi sym :=
  match sym with
  | T y  => StringSet.singleton y
  | NT x => match StringMap.find x fi with
            | Some se => se
            | None    => StringSet.empty
            end
  end.

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
  match StringMap.find k m with
  | Some v => v
  | None   => StringSet.empty
  end.

(*Definition beqString sy sy2 := if StringAsDT.eq_dec sy sy2 then true else false. *)

Definition beqString s s2 := if string_dec s s2 then true else false.

Definition tokenize s :=
  let singletonString (a : Ascii.ascii) :=
      String a EmptyString
  in
  let fix tokenize' (s : string)
                    (t : string)
                    (ts : list string)
                    : list string :=
      match s with
      | EmptyString => (ts ++ [t])%list
      | String a s' =>
        match nat_of_ascii a with
        | 32 => (* space token *)
          tokenize' s' "" (ts ++ [t])%list
        | _   => tokenize' s' (t ++ singletonString a) ts
        end
      end
  in  tokenize' s "" nil.

Fixpoint beqList (xs ys : list string) : bool :=
  match (xs, ys) with
  | (nil, nil) => true
  | (x :: xs', y :: ys') =>
    if beqString x y then beqList xs' ys' else false
  | _ => false
  end.

Definition elem {A : Type} (x : A)
                           (l : list A)
                           (cmp : A -> A -> bool)
                           : bool :=
  match find (cmp x) l with
  | Some _ => true
  | None   => false
  end.

Definition nub {A : Type} (xs : list A) (cmp : A -> A -> bool) : list A :=
  fold_right (fun x acc => if elem x acc cmp then acc else x :: acc) nil xs.

Lemma beqSym_eq : forall x y,
    beqString x y = true <-> x = y.
Proof.
  intros; split; intros.
  - unfold beqString in H. destruct (StringMapFacts.eq_dec).
    + subst; reflexivity.
    + inversion H.
  - unfold beqString. destruct (StringMapFacts.eq_dec).
    + reflexivity.
    + exfalso. apply n. assumption.
Qed.

Definition rhss (g : grammar) (x : string) :=
  map snd (filter (fun prod => beqString (fst prod) x) g.(productions)).

Lemma rhss_in_grammar : forall g x gammas gamma,
    rhss g x = gammas ->
    In gamma gammas ->
    In (x, gamma) g.(productions).
Proof.
  intros. unfold rhss in H.
  subst. rewrite in_map_iff in H0.
  destruct H0 as [prod].
  destruct prod as (l, r); simpl in H; destruct H.
  rewrite filter_In in H0. destruct H0.
  rewrite beqSym_eq in H1; simpl in H1.
  subst. assumption.
Qed.

Definition removeOpt (x : symbol) (s : SymbolSet.t) :=
  if SymbolSet.mem x s then
    Some (SymbolSet.remove x s)
  else None.

Definition addAll (xs : list symbol) : SymbolSet.t :=
  fold_right SymbolSet.add SymbolSet.empty xs.

Definition unionAll (ss : list SymbolSet.t) : SymbolSet.t :=
  fold_right SymbolSet.union SymbolSet.empty ss.

Definition nonterminals g :=
  let prodNTs p :=
      match p with
      | (l, rs) =>
        SymbolSet.add (NT l) (addAll (filter isNT rs))
      end
  in  unionAll (map prodNTs g).
