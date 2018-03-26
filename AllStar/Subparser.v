Require Import Bool FunctionalExtensionality List Omega String.
Require Import Grammar Lib.Lemmas Lib.Tactics Lib.Utils.
Import ListNotations.
Open Scope string_scope.

Record subparser :=
  mkSp { stack: list symbol ;
         pred : list symbol }.

(* Two subparsers are equal if their stacks 
   and predictions are equal. *)
Definition beqSp (sp sp2 : subparser) : bool :=
  beqList sp.(stack) sp2.(stack) &&
  beqList sp.(pred) sp2.(pred).

Section spClosure.

  Definition pairOrder (p1 p2 : SymbolSet.t * list symbol) :=
    match (p1, p2) with
    | ((s1, _), (s2, _)) =>
      SymbolSet.cardinal s1 < SymbolSet.cardinal s2
    end.

  Lemma pairOrder_wf' : forall card s2 sp2,
      SymbolSet.cardinal s2 <= card ->
      Acc pairOrder (s2, sp2).
  Proof.
    induction card as [| n]; intros; constructor;
      intros pair1 Horder.
    - destruct pair1 as (s1, sp1).
      unfold pairOrder in Horder. omega.
    - destruct pair1 as (s1, sp1).
      apply IHn.
      unfold pairOrder in Horder. omega.
  Defined.

  Lemma pairOrder_wf : well_founded pairOrder.
  Proof.
    red. intro pair.
    destruct pair as [s sp].
    apply pairOrder_wf' with (card := SymbolSet.cardinal s).
    trivial.
  Defined.

(* Proving this arithmetic fact as a separate lemma 
   might result in a smaller proof term -- I'm not sure. *)
Lemma Sn_eq_n_lt : forall n m,
    S n = m -> n < m.
Proof.
  intros. abstract omega.
Qed.

(* This fact appears in SymbolSetEqProps, but I'm proving
   it again here and making the definition transparent. *)
Lemma In_dec':
  forall (x : SymbolSet.elt) (s : SymbolSet.t),
    {SymbolSet.In x s} + {~ SymbolSet.In x s}.
Proof.
  intros. pose proof (SymbolSetFacts.mem_iff s x) as H_mem.
  destruct (SymbolSet.mem x s).
  - left. apply H_mem. trivial.
  - right. unfold not; intros.
    apply H_mem in H. inversion H.
Defined.

Lemma In_dec'':
  forall (x : SymbolSet.elt) (s : SymbolSet.t),
    {SymbolSet.In x s} + {~ SymbolSet.In x s}.
Proof.
  apply SymbolSetEqProps.MP.In_dec.
Defined.

Definition gammaClosure (g : grammar) :
  SymbolSet.t * list symbol -> list (list symbol).
  refine
    (Fix pairOrder_wf
         (fun _ => _)
         (fun (pr : SymbolSet.t * list symbol)
              (gammaClosure : forall pr',
                  pairOrder pr' pr -> list (list symbol)) =>
            match snd pr with
            | nil => [snd pr]
            | T _ :: _ => [snd pr]
            | NT x :: gamma' =>
              if In_dec' (NT x) (fst pr) then
                let newGammas :=
                    map (fun rhs => app rhs gamma')
                        (rhss g x)
                in  flat_map
                      (fun ng =>
                         gammaClosure (SymbolSet.remove (NT x) (fst pr), ng) _)
                      newGammas
              else
                nil
            end)).
  - unfold pairOrder.
    destruct pr as (freeSyms0, gamma).
    simpl; simpl in i.
    apply Sn_eq_n_lt.
    apply SymbolSetEqProps.remove_cardinal_1.
    rewrite <- SymbolSet.mem_spec in i.
    assumption.
Defined.

Lemma gammaClosureUnfold :
  forall g pr,
    gammaClosure g pr =
    match snd pr with
    | nil => [snd pr]
    | T _ :: _ => [snd pr]
    | NT x :: gamma' =>
      if In_dec' (NT x) (fst pr) then
        let newGammas :=
            map (fun rhs => app rhs gamma')
                (rhss g x)
        in  flat_map
              (fun ng =>
                 gammaClosure g (SymbolSet.remove (NT x) (fst pr), ng))
              newGammas
      else
        nil
    end.
Proof.
  intros. unfold gammaClosure.
  apply Fix_eq with (A := (SymbolSet.t * list symbol)%type)
                    (R := pairOrder)
                    (Rwf := pairOrder_wf)
                    (P := fun _ => list (list symbol)).
  intros; simpl.
  destruct (snd x).
  - reflexivity.
  - destruct s as [tName | ntName].
    + reflexivity.
    + destruct (In_dec' (NT ntName) (fst x)).
      * repeat f_equal.
        apply functional_extensionality; intros.
        repeat f_equal.
        extensionality p; extensionality lt.
        apply H.
      * reflexivity.
Qed.

(*
Definition spClosure' (g : grammar) :
      SymbolSet.t * subparser -> list subparser.
      refine
        (Fix
           pairOrder_wf
           (fun  _ => _)
           (fun (pr : SymbolSet.t * subparser)
                (spClosure' : forall pr',
                    pairOrder pr' pr -> list subparser) =>
              match (snd pr).(stack) with
              | nil => [snd pr]
              | T _ :: _ => [snd pr]
              | NT x :: stack' =>
                if (In_dec' (NT x) (fst pr)) then
                  let newSps :=
                      map (fun gamma =>
                             {| stack := gamma ++ stack';
                                pred  := (snd pr).(pred) |})
                          (rhss g x)
                  in  flat_map (fun sp =>
                                  spClosure' ((SymbolSet.remove (NT x) (fst pr)), sp) _)
                               newSps
                else
                  nil
              end)).
      (* We have one proof obligation: showing that the
         "freeSyms" set is getting smaller *)
      - unfold pairOrder. destruct pr as (freeSyms0, sp0).
        simpl; simpl in i.
        apply Sn_eq_n_lt.
        apply (SymbolSetEqProps.remove_cardinal_1
                 freeSyms0 (NT x)).
        rewrite <- SymbolSet.mem_spec in i.
        assumption.
Defined.
 *)

(* Lemma for unfolding spClosure' to get the expected body *)

(*
Lemma spClosure'Unfold : forall g pr,
    spClosure' g pr =
    match (snd pr).(stack) with
              | nil => [snd pr]
              | T _ :: _ => [snd pr]
              | NT x :: stack' =>
                if (In_dec' (NT x) (fst pr)) then
                  let newSps :=
                      map (fun gamma =>
                             {| stack := gamma ++ stack';
                                pred  := (snd pr).(pred) |})
                          (rhss g x)
                  in  flat_map (fun sp =>
                                  spClosure' g ((SymbolSet.remove (NT x) (fst pr)), sp))
                               newSps
                else
                  nil
              end.
Proof.
  intros. unfold spClosure'. 
  apply Fix_eq with (A := (SymbolSet.t * subparser)%type)
                    (R := pairOrder)
                    (Rwf := pairOrder_wf)
                    (P := fun _ => list subparser).
  intros. simpl.
  destruct (stack (snd x)).
  - reflexivity.
  - destruct s as [tName | ntName].
    + reflexivity.
    + destruct (In_dec' (NT ntName) (fst x)).
      * repeat f_equal.
        apply functional_extensionality; intros.
        repeat f_equal.
        extensionality y. extensionality p.
        apply H.
      * reflexivity.
Qed.
*)

Definition spClosure g freeSyms sp :=
  map (fun gamma => {| stack := gamma; pred := sp.(pred) |})
      (gammaClosure g (freeSyms, sp.(stack))).

End spClosure.

Definition move (token : string) (sps : list subparser) :
                list subparser :=
  let moveSp sp := 
      match sp.(stack) with
      | nil => [sp]
      | NT _ :: _ => nil (* implementation error? *)
      | T y :: stack' =>
        if beqSym (T y) (T token) then 
          [mkSp stack' sp.(pred)] 
        else 
          nil
      end 
  in  concat (map moveSp sps).

Definition closure (g : grammar) (freeSyms : SymbolSet.t)
           (sps : list subparser) : list subparser :=
  flat_map (spClosure g freeSyms) sps.

(* LL predict when stack0 is nil, SLL predict otherwise *)
Definition startState (g : grammar) (x : string)
                      (stack0 : list symbol) :
                      list subparser :=
  let sps := map (fun gamma =>
                    mkSp (gamma ++ stack0) gamma)
                 (rhss g x)
  in  closure g (nonterminals g) sps.

Definition target (g : grammar) (sps : list subparser)
                  (token : string) : list subparser :=
  closure g (nonterminals g) (move token sps).

Fixpoint conflict (sps : list subparser) : bool :=
  match sps with
  | nil => false
  | sp :: sps' => 
    if existsb
         (fun sp2 => 
            beqList sp.(stack) sp2.(stack) && 
            negb (beqList sp.(pred) sp2.(pred)))
         sps'
    then true
    else conflict sps'
  end.

Inductive pred_result := 
| Choice   : list symbol -> pred_result
| Conflict : list subparser -> pred_result
| Fail     : pred_result.  

Fixpoint predict (g : grammar) (sps : list subparser)
                 (input : list string) : pred_result :=
  (*let preds := map pred sps in *)
  match nub sps (fun sp sp2 => beqList sp.(pred) sp2.(pred)) with
  | nil => Fail
  | [p] => Choice p.(pred)
  | _ => if conflict sps then
           Conflict sps
         else
           match input with
           | nil => Fail (*actually, check for final configs*)
           | token :: input' => 
             predict g (target g sps token) input'
           end
  end.

(* For now, the only difference between sllPredict and
   llPredict is the "initial stack" argument that they pass to
   startState. This will change when sllPredict starts using a 
   cache. *)
Definition sllPredict (g : grammar) (x : string)
                      (input : list string) : pred_result :=
  let state0 := startState g x nil in
  predict g state0 input.

Definition llPredict (g : grammar)  (x : string)
                     (input : list string)
                     (stack0 : list symbol) : pred_result :=
  let state0 := startState g x stack0 in
  predict g state0 input.

Definition adaptivePredict (g : grammar) (x : string)
                           (input : list string)
                           (stack0 : list symbol) :
                           pred_result :=
  let sllPred := sllPredict g x input in
  match sllPred with
  | Conflict _ => llPredict g x input stack0
  | _ => sllPred
  end.
