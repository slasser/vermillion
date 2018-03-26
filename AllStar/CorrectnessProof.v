Require Import List Omega String.
Require Import Lib.Derivation Lib.Grammar Lib.Lemmas
               Lib.ParseTree Lib.Tactics Lib.Utils.
Require Import AllStar.Parser AllStar.Subparser.
Import ListNotations.

Lemma nt_derives_Node :
  forall g x input stack fuel tree suffix,
    parse' g (NT x) input stack fuel = (Some tree, suffix) ->
    isNode tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct (adaptivePredict g x input stack).
    + destruct (parseForest g l input stack fuel).
      destruct o.
      * inv H. reflexivity.
      * inv H.
    + inv H.
    + inv H.
Qed.

Lemma t_derives_Leaf :
  forall g y input stack fuel tree suffix,
    parse' g (T y) input stack fuel = (Some tree, suffix) ->
    isLeaf tree = true.
Proof.
  intros. destruct fuel.
  - simpl in H. inv H.
  - simpl in H. destruct input.
    + inv H.
    + destruct (beqSym (T y) (T s)).
      * inv H. reflexivity.
      * inv H.
Qed.

(* Here are the lemmas we need to fill the gap in the proof below. *)

Lemma beqSym_eq : forall x y,
    beqSym x y = true <-> x = y.
Proof.
  intros; split; intros.
  - unfold beqSym in H. destruct (SymbolMapFacts.eq_dec).
    + subst; reflexivity.
    + inv H.
  - unfold beqSym. destruct (SymbolMapFacts.eq_dec).
    + reflexivity.
    + exfalso. apply n. assumption.
Qed.

(* Not needed anymore, since we proved this fact
   about the version of rhss in Utils *)
(*
Lemma rhss_in_grammar : forall g ntName yss ys,
    rhss g ntName = yss ->
    In ys yss ->
    In (NT ntName, ys) g.
Proof.
  intro g.
  induction g as [| prod g']; intros ntName yss ys Hrhss Hin;
  simpl.
  - simpl in Hrhss. rewrite <- Hrhss in Hin. inv Hin.
  - destruct prod as [l r]; subst. simpl in Hin.
    destruct (beqSym l (NT ntName)) eqn:Heq.
    + rewrite beqSym_eq in Heq. simpl in Hin.
      destruct Hin as [Hhd | Htl].
      * left. subst. reflexivity.
      * right. eapply IHg'; [reflexivity | assumption].
    + right. eapply IHg'; [reflexivity | assumption].
Qed.
*)

Lemma spClosure_preserves_pred :
  forall g freeSyms sp sps sp',
    spClosure g freeSyms sp = sps ->
    In sp' sps ->
    sp.(pred) = sp'.(pred).
Proof.
  intros. unfold spClosure in H.
  subst.
  induction (gammaClosure g (freeSyms, stack sp))
    as [| gamma gammas].
  - simpl in H0. inv H0.
  - destruct H0.
    + subst. simpl. reflexivity.
    + apply IHgammas. assumption.
Qed.

Lemma closure_preserves_preds :
  forall g freeSyms sps sp' sps',
    closure g freeSyms sps = sps' ->
    In sp' sps' ->
    exists sp,
      In sp sps /\ sp.(pred) = sp'.(pred).
Proof.
  induction sps as [| sp sps]; intros.
  - simpl in H. subst. inv H0.
  - unfold closure in H.
    subst. simpl in H0.
    apply in_app_or in H0.
    destruct H0.
    + exists sp. split.
      * apply in_eq.
      * eapply spClosure_preserves_pred.
        { reflexivity. }
        { eassumption. }
    + edestruct IHsps.
      * reflexivity.
      * unfold closure. eassumption.
      * destruct H0.
        exists x. split.
        { apply in_cons. assumption. }
        { assumption. }
Qed.
    
Lemma startState_in_grammar :
  forall g x stack0 sps sp gamma,
    startState g x stack0 = sps ->
    In sp sps ->
    sp.(pred) = gamma ->
    In (NT x, gamma) g.
Proof.
  intros.
  unfold startState in H.
  eapply closure_preserves_preds in H.
  - destruct H as [sp0]; destruct H.
    rewrite in_map_iff in H.
    destruct H as [gamma0]; destruct H.
    subst. simpl in H2. subst.
    eapply Utils.rhss_in_grammar.
    + reflexivity.
    + eassumption.
  - assumption.
Qed.

Lemma nub_In :
  forall A (x : A) xs xs' f,
    nub xs f = xs' ->
    In x xs' ->
    In x xs.
Proof.
  induction xs as [| hd tl]; intros.
  - simpl in H. subst. inv H0.
  - simpl in H.
    destruct (elem hd (nub tl f) f) eqn:Helem.
    + apply IHtl in H.
      * apply in_cons. assumption.
      * assumption.
    + subst. destruct H0.
      * subst. apply in_eq.
      * eapply IHtl in H.
        { apply in_cons. assumption. }
        { reflexivity. }
Qed.

Lemma move_preserves_preds :
  forall token sps sp',
    In sp' (move token sps) ->
    exists sp,
      In sp sps /\ sp.(pred) = sp'.(pred).
Proof.
  intros. unfold move in H.
  induction sps as [| sp sps]; simpl in H.
  - inv H.
  - apply in_app_or in H. destruct H.
    + destruct (stack sp).
      * inv H.
        { exists sp'; split.
          { apply in_eq. }
          { reflexivity. }}
        { inv H0. }
      * destruct s as [tName | ntName].
        { destruct (beqSym (T tName) (T token)).
          { inv H.
            { exists sp; split.
              { apply in_eq. }
              { simpl. reflexivity. }}
            { inv H0. }}
          { inv H. }}
        { inv H. }
    + apply IHsps in H. clear IHsps.
      destruct H as [sp'']; destruct H.
      exists sp''; split.
      * apply in_cons. assumption.
      * assumption.
Qed.
    
Lemma target_preserves_preds :
  forall g sps token sp',
    In sp' (target g sps token) ->
    exists sp,
      In sp sps /\ sp.(pred) = sp'.(pred).
Proof.
  intros. unfold target in H.
  eapply closure_preserves_preds with
      (sps := move token sps) in H.
  -  destruct H as [sp]; destruct H.
     apply move_preserves_preds in H.
     destruct H as [sp0]; destruct H.
     exists sp0; split.
     + assumption.
     + rewrite H1. assumption.
  - reflexivity.
Qed.
  
Lemma predict_preserves_preds :
  forall g input ys sps,
    predict g sps input = Choice ys ->
    exists sp,
      In sp sps /\ sp.(pred) = ys.
Proof.
  induction input as [| token tokens]; intros.
  - unfold predict in H.
    destruct (nub sps
          (fun sp sp2 : subparser =>
           beqList (pred sp) (pred sp2))) eqn:Hnub.
    + inv H.
    + destruct l.
      * inv H.
        exists s. split.
        { eapply nub_In.
          { reflexivity. }
          { rewrite Hnub. apply in_eq. }}
        { reflexivity. }
      * destruct (conflict sps); inv H.
  - unfold predict in H.
    destruct (nub sps
          (fun sp sp2 : subparser =>
             beqList (pred sp) (pred sp2))) eqn:Hnub.
    + inv H.
    + destruct l.
      * inv H.
        exists s; split.
        { eapply nub_In.
          { reflexivity. }
          {  rewrite Hnub. apply in_eq. }}
        { reflexivity. }
      * destruct (conflict sps).
        { inv H. }
        { unfold predict in IHtokens.
          apply IHtokens in H. clear IHtokens.
          destruct H as [sp']; destruct H.
          apply target_preserves_preds in H.
          subst. assumption. }
Qed.
            
Lemma sllPredict_result_in_grammar :
  forall g x input ys,
    sllPredict g x input = Choice ys ->
    In (NT x, ys) g.
Proof.
  intros. unfold sllPredict in H.
  apply predict_preserves_preds in H.
  destruct H as [sp]; destruct H.
  eapply startState_in_grammar in H.
  - eassumption.
  - reflexivity.
  - assumption.
Qed.

Lemma llPredict_result_in_grammar :
  forall g x input stack0 ys,
    llPredict g x input stack0 = Choice ys ->
    In (NT x, ys) g.
Proof.
  intros. unfold llPredict in H.
  apply predict_preserves_preds in H.
  destruct H as [sp]; destruct H.
  eapply startState_in_grammar in H.
  - eassumption.
  - reflexivity.
  - assumption.
Qed.

Lemma adaptivePredict_result_in_grammar :
  forall g x input stack0 ys,
    adaptivePredict g x input stack0 = Choice ys ->
    In (NT x, ys) g.
Proof.
  intros. unfold adaptivePredict in H.
  destruct (sllPredict g x input) eqn:Hsll.
  - inv H.
    eapply sllPredict_result_in_grammar.
    eassumption.
  - eapply llPredict_result_in_grammar.
    eassumption.
  - inv H.
Qed.

Theorem parse'_correct :
  forall (g      : grammar)
         (tr     : tree)
         (sym    : symbol)
         (input  : list string)
         (stack  : list symbol)
         (fuel   : nat)
         (suffix : list string),
    parse' g sym input stack fuel = (Some tr, suffix) ->
    exists (prefix : list string),
      (prefix ++ suffix)%list = input /\
      (@derivesTree g) sym prefix tr.
Proof.
  intros g tr.
  induction tr as [ s
                  | s f IHparseForest
                  |
                  | tr IHparse f IHparseForest ]
      using tree_mutual_ind with
      (P := fun tr =>
              forall sym input stack fuel suffix,
                parse' g sym input stack fuel =
                (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr)
      (P0 := fun subtrees =>
               forall gamma input stack fuel suffix,
                 parseForest g gamma input stack fuel =
                 (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees).
  - intros sym input stack fuel suffix Hparse'.
    destruct fuel as [| fuel].
    + inv Hparse'.
    + destruct sym as [y | x].
      * destruct input as [| token input].
        { inv Hparse'. }
        simpl in Hparse'.
        destruct (beqSym (T y) (T token)) eqn:Hbeq.
        { inv Hparse'. exists [token]. split.
          { reflexivity. }
          apply eq_sym_eq_T in Hbeq. subst. apply derivesT. }
        inv Hparse'.
      * apply nt_derives_Node in Hparse'. inv Hparse'.
  - (* 2nd case *)
    intros sym input stack fuel suffix Hparse'.
    destruct fuel as [| fuel].
    + inv Hparse'.
    + destruct sym as [y | x].
      * apply t_derives_Leaf in Hparse'. inv Hparse'.
      * simpl in Hparse'.
        destruct (adaptivePredict g x input stack)
                 as [ys | sps | ] eqn:Hpred.
        { destruct (parseForest g ys input stack fuel)
            as [subresult input'] eqn:Hforest.
          destruct subresult as [subtrees |].
          { inv Hparse'. apply IHparseForest in Hforest.
            clear IHparseForest.
            destruct Hforest as [prefix Hforest].
            exists prefix.
            destruct Hforest as [Happ Hderives]. split.
            { assumption. }
            inv Hderives.
            { apply derivesNT with (gamma := nil).
              { (* Here's where we need a lemma saying that
                   whenever adaptivePredict returns Choice ys,
                   ys is in the grammar. *)
                eapply adaptivePredict_result_in_grammar.
                eassumption. }
              apply derivesFnil. }
            eapply derivesNT.
            { eapply adaptivePredict_result_in_grammar.
              eassumption. }
            eapply derivesFcons.
            { eassumption. }
            eassumption. }
          inv Hparse'. }
        { inv Hparse'. }
        inv Hparse'.
  - intros gamma input stack fuel suffix HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * simpl in HparseForest. inv HparseForest.
        exists nil. split.
        { reflexivity. }
        apply derivesFnil.
      * exfalso.
        simpl in HparseForest.
        destruct (parse' g sym input (gamma' ++ stack) fuel)
          as [subresult input'].
         destruct subresult as [lSib |].
         { destruct (parseForest g gamma' input' stack fuel)
             as [subresult input''].
           destruct subresult as [rSibs |].
           { inv HparseForest. }
           inv HparseForest. }
         inv HparseForest.
  - intros gamma input stack fuel suffix HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * inv HparseForest.
      * simpl in HparseForest.
        destruct (parse' g sym input (gamma' ++ stack) fuel)
          as [subresult input'] eqn:Htree.
        destruct subresult.
        { destruct (parseForest g gamma' input' stack fuel)
            as [subresult input''] eqn:Hforest.
          destruct subresult as [rSibs |].
          { inv HparseForest.
            apply IHparse in Htree. clear IHparse.
            destruct Htree as [treePrefix Htree].
            destruct Htree as [HappTree HderivesTree].
            apply IHparseForest in Hforest. clear IHparseForest.
            destruct Hforest as [forestPrefix Hforest].
            destruct Hforest as [HappForest HderivesForest].
            subst.
            exists (treePrefix ++ forestPrefix)%list. split.
            { rewrite app_assoc. reflexivity. }
            apply derivesFcons.
            { assumption. }
            assumption. }
          inv HparseForest. }
        inv HparseForest.
Qed.

Theorem parse_correct :
  forall (g      : grammar)
         (tr     : tree)
         (sym    : symbol)
         (input  : list string)
         (fuel   : nat)
         (suffix : list string),
    parse g sym input fuel = (Some tr, suffix) ->
    exists (prefix : list string),
      (prefix ++ suffix)%list = input /\
      (@derivesTree g) sym prefix tr.
Proof.
  intros. eapply parse'_correct. eassumption.
Qed.
