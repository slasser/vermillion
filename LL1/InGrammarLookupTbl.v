Require Import LL1.Parser ParseTable Derivation Grammar ParseTree Lib.Tactics LL1.CorrectnessProof.
Require Import List String.
Import ListNotations.

Inductive nullableProd {g : grammar} :
  nonterminal -> list symbol -> Prop :=
| n_prod :
    forall x ys,
      In (x, ys) g.(productions)
      -> nullableGamma ys
      -> nullableProd x ys
with nullableGamma {g : grammar} :
       list symbol -> Prop :=
     | n_nil :
         nullableGamma nil
     | n_cons :
         forall x tl,
           nullableSym x
           -> nullableGamma tl
           -> nullableGamma (NT x :: tl)
with nullableSym {g : grammar} :
       nonterminal -> Prop :=
     | n_sym :
         forall x ys,
           nullableProd x ys
           -> nullableSym x.

Inductive firstProd {g : grammar} :
    lookahead -> nonterminal -> list symbol -> Prop :=
| first_prod : forall la x gamma,
    In (x, gamma) g.(productions)
    -> firstGamma la gamma
    -> firstProd la x gamma
with firstGamma {g : grammar} :
       lookahead -> list symbol -> Prop :=
     | fgamma_hd : forall la hd tl,
         firstSym la hd ->
         firstGamma la (hd :: tl)
     | fgamma_tl : forall la x tl,
         (@nullableSym g) x ->
         firstGamma la tl ->
         firstGamma la (NT x :: tl)
with firstSym {g : grammar} :
       lookahead -> symbol -> Prop :=
| first_t : forall s,
    firstSym (LA s) (T s)
| first_nt : forall la x gamma,
    firstProd la x gamma ->
    firstSym la (NT x).

Inductive followProd {g : grammar} :
  lookahead -> nonterminal -> list symbol -> Prop :=
| follow_prod :
    forall la x gamma,
      In (x, gamma) g.(productions)
      -> followSym la x
      -> followProd la x gamma
with followSym {g : grammar} :
       lookahead -> nonterminal -> Prop :=
     | f_start :
         followSym EOF g.(start)
     | f_right :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@firstGamma g) la suffix
           -> followSym la x2
     | f_left :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@nullableGamma g) suffix
           -> followSym la x1
           -> followSym la x2.

Definition isLookaheadFor {g} la x gamma :=
  (@firstProd g) la x gamma
  \/ (@nullableProd g) x gamma /\ (@followProd g) la x gamma.

Definition ptMinimal tbl g :=
  forall x la gamma laMap,
    StringMap.find x tbl = Some laMap
    -> LookaheadMap.find la laMap = Some gamma
    -> (@isLookaheadFor g) la x gamma.

Definition ptComplete tbl g :=
  forall x la gamma,
    (@isLookaheadFor g) la x gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.

Definition isParseTableFor (tbl : parse_table)  (g : grammar)  := ptMinimal tbl g /\ ptComplete tbl g.

Theorem parseForest_correct :
  forall (g   : grammar)
         (tbl : parse_table),
    ParseTable.isParseTableFor tbl g ->
    forall f input gamma suffix fuel,
      parseForest tbl gamma input fuel =
      (Some f, suffix) ->
      exists prefix,
        (prefix ++ suffix)%list = input /\
        (@derivesForest g) gamma prefix f.
Proof.
  intros g tbl Htbl f.
  induction f using forest_mutual_ind with
      (P0 := fun subtrees =>
               forall input gamma suffix fuel,
                 parseForest tbl gamma input fuel =
                 (Some subtrees, suffix) ->
                 exists prefix,
                   (prefix ++ suffix)%list = input /\
                   (@derivesForest g) gamma prefix subtrees)
      (P := fun tr =>
              forall input sym suffix fuel,
                parse tbl sym input fuel = (Some tr, suffix) ->
                exists prefix,
                  (prefix ++ suffix)%list = input /\
                  (@derivesTree g) sym prefix tr).

  - intros input sym suffix fuel Hparse. 
    destruct fuel as [| fuel].
    + inv Hparse.
    + destruct sym as [y | x].
      * destruct input as [| token input].
        { inv Hparse. }
        simpl in Hparse.
        destruct (Utils.beqString y token) eqn:Hbeq.
        { inv Hparse. exists [token]. split.
          { reflexivity. }
          apply beqString_eq in Hbeq. subst.
          apply derivesT. }
        inv Hparse.
      * apply nt_derives_Node in Hparse. inv Hparse.

  - intros input sym suffix fuel Hparse.
    destruct fuel as [| fuel].
    + inv Hparse.
    + destruct sym as [y | x].
      * apply t_derives_Leaf in Hparse. inv Hparse.
      * simpl in Hparse. 
        destruct (parseTableLookup x (peek input) tbl)
                 as [ys |] eqn:Hlookup.
        { destruct (parseForest tbl ys input fuel)
                   as [subresult input'] eqn:Hforest.
          { destruct subresult as [subtrees |].
            { inv Hparse.
              apply IHf in Hforest.
              destruct Hforest as [prefix Hforest].
              exists prefix.
              destruct Hforest as [Happ Hderives]. split.
              { assumption. }
              inv Hderives.
              { apply derivesNT with (gamma := nil).
                { simpl in Hlookup. 
                  apply lookup_tbl_in_grammar with
                      (g := g)
                      (x := s)
                      (y := peek suffix)
                      (gamma:=nil) in Hlookup.
                  { assumption. }
                  assumption. }
                apply derivesFnil. }
              apply derivesNT with
                  (gamma := (hdRoot :: tlRoots)).
              { eapply lookup_tbl_in_grammar; eassumption. }
              { apply derivesFcons; assumption. }}
            { inv Hparse. }}}
        { inv Hparse. }

  - intros input gamma suffix fuel HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * simpl in HparseForest. inv HparseForest.
        exists nil. split.
        { reflexivity. }
        apply derivesFnil.
      * exfalso.
        simpl in HparseForest.
        destruct (parse tbl sym input fuel)
          as [subresult input'].
        destruct subresult as [lSib |].
        { destruct (parseForest tbl gamma' input' fuel)
            as [subresult input''].
          destruct subresult as [rSibs |].
          { inv HparseForest. }
          inv HparseForest. }
        inv HparseForest.

  - intros input gamma suffix fuel HparseForest.
    destruct fuel as [| fuel].
    + inv HparseForest.
    + destruct gamma as [| sym gamma'].
      * inv HparseForest.
      * simpl in HparseForest.
        destruct (parse tbl sym input fuel)
          as [subresult input'] eqn:Htree.
        destruct subresult.
        { destruct (parseForest tbl gamma' input' fuel)
            as [subresult input''] eqn:Hforest.
          destruct subresult as [rSibs |].
          { inv HparseForest.
            apply IHf in Htree.
            { destruct Htree as [treePrefix Htree].
              destruct Htree as [HappTree HderivesTree].
              apply IHf0 in Hforest.
              destruct Hforest as [forestPrefix Hforest].
              destruct Hforest as [HappForest HderivesForest].
              subst.
              exists (treePrefix ++ forestPrefix)%list. split.
              { rewrite app_assoc. reflexivity. }
              apply derivesFcons.
              { assumption. }
              assumption. }}
          inv HparseForest. }
        inv HparseForest.
Qed.



Lemma lookup_exists :
  forall x la tbl gamma,
    parseTableLookup x la tbl = Some gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.
Proof.
  intros.
  unfold parseTableLookup in H.
  destruct (StringMap.find x tbl) as [laMap |] eqn:Hsf.
  - exists laMap; split; trivial.
  - inv H.
Qed.

Scheme firstprod_ind := Induction for firstProd Sort Prop
  with firstgamma_ind := Induction for firstGamma Sort Prop
  with firstsym_ind := Induction for firstSym Sort Prop.

Lemma eof_fprod :
  forall g la x gamma,
    (@firstProd g) la x gamma
    -> la = EOF
    -> False.
Proof.
  intros g la x gamma H.
  induction H using firstprod_ind with
      (P := fun la x gamma (pf : firstProd la x gamma) =>
              la = EOF -> False)
      (P0 := fun la gamma (pf : firstGamma la gamma) =>
               la = EOF -> False)
      (P1 := fun la sym (pf : firstSym la sym) =>
               la = EOF -> False); intros.
  - apply IHfirstProd; trivial.
  - apply IHfirstProd; trivial.
  - apply IHfirstProd; trivial. 
  - inv H.
  - apply IHfirstProd; trivial.
Qed.

Lemma eof_fgamma :
  forall g la gamma,
    (@firstGamma g) la gamma
    -> la = EOF
    -> False.
Proof.
  intros g la gamma H.
  induction H using firstgamma_ind with
      (P := fun la x gamma (pf : firstProd la x gamma) =>
              la = EOF -> False)
      (P0 := fun la gamma (pf : firstGamma la gamma) =>
               la = EOF -> False)
      (P1 := fun la sym (pf : firstSym la sym) =>
               la = EOF -> False); intros.
  - apply IHfirstGamma; trivial.
  - apply IHfirstGamma; trivial.
  - apply IHfirstGamma; trivial. 
  - inv H.
  - apply IHfirstGamma; trivial.
Qed.



Lemma eof_nullable :
  forall gamma tbl g x,
    isParseTableFor tbl g
    -> parseTableLookup x EOF tbl = Some gamma
    -> exists f,
        (@derivesForest g) gamma [] f.
Proof.
  induction gamma as [| sym syms]; intros.
  - exists Fnil. constructor.
  - apply lookup_exists in H0.
    destruct H0 as [laMap [Hsf Hlf]].
    destruct H as [Hmin Hcom].
    unfold ptMinimal in Hmin.
    apply Hmin with (la := EOF) (gamma := sym :: syms) in Hsf.
    + destruct Hsf.
      * apply eof_fprod in H; inv H; trivial.
      * destruct H as [Hnp Hfp].
        inv Hnp.
        inv H0.
        inv H3.
        inv Hfp.
Abort.
      

(* This would solve the goal *)
Lemma gamma_gamma' :
  forall gamma gamma' tbl g x prefix suffix fuel f f' suffix',
    isParseTableFor tbl g
    -> parseTableLookup x (peek (prefix ++ suffix)) tbl =
       Some gamma'
    -> In (x, gamma) (productions g)
    -> parseForest tbl gamma (prefix ++ suffix) fuel =
       (Some f, suffix)
    -> parseForest tbl gamma' (prefix ++ suffix) fuel =
       (Some f', suffix')
    -> gamma = gamma'.
Proof.
  induction gamma as [| sym syms].
  - induction gamma' as [| sym' syms']; intros.

    + trivial.

    + exfalso.
      apply parseForest_correct with (g := g) in H2.
      * destruct H2 as [pre [Happ Hder]].
        assert (pre = prefix).
        { admit. }
        subst.
        inv Hder.
        simpl in *.
        destruct H as [Hmin Hcom].
        destruct suffix as [| tok toks].
        -- simpl in *.
           unfold ptMinimal in Hmin.
           apply lookup_exists in H0.
           destruct H0 as [laMap [Hsfind Hlfind]].
           apply Hmin with (la := EOF)
                           (gamma := sym' :: syms') in Hsfind.
           ++ destruct Hsfind as [Hfi | Hfo].
              ** apply eof_fprod in Hfi.
                 --- inv Hfi.
                 --- trivial.
              ** destruct Hfo as [Hnp Hfp].
                 inv Hfp.
                 inv H0.
                 --- unfold ptComplete in Hcom.
                     assert (Hlk : (@isLookaheadFor g)  EOF (start g)
                                                    []).
                     { unfold isLookaheadFor.
                       right.
                       split.
                       { constructor. trivial. constructor. }
                       { constructor. trivial. constructor. }}
                     assert (Hlk' : (@isLookaheadFor g)
                                     EOF
                                     (start g)
                                     (sym' :: syms')).
                     { unfold isLookaheadFor.
                       right.
                       split.
                       { trivial. }
                       { constructor.
                         trivial.
                         constructor. }}
                     apply Hcom in Hlk.
                     apply Hcom in Hlk'.
                     destruct Hlk as [map [map1 map2]].
                     destruct Hlk' as [map' [map1' map2']].
                     congruence.
                 --- apply eof_fgamma in H4.
                     +++ inv H4.
                     +++ trivial.
                 --- assert (Hlk : (@isLookaheadFor g)
                                     EOF
                                     x
                                     []).
                     +++ unfold isLookaheadFor.
                         right.
                         split.
                         *** constructor.
                             trivial.
                             constructor.
                         *** constructor.
                             trivial.
                             eapply f_left.
                             ---- eassumption.
                             ---- trivial.
                             ---- trivial.
                     +++ assert (Hlk' : (@isLookaheadFor g)
                                          EOF
                                          x
                                          (sym' :: syms')).
                         { unfold isLookaheadFor.
                           right.
                           split.
                           { trivial. }
                           { constructor.
                             trivial.
                             eapply f_left; eauto. }}
                         apply Hcom in Hlk.
                         apply Hcom in Hlk'.
                         destruct Hlk.
                         destruct Hlk'.
                         destruct H0.
                         destruct H6.
                         congruence.
           ++ trivial.
              
        -- simpl in *.
           unfold ptMinimal in Hmin.
           apply lookup_exists in H0.
           destruct H0 as [map [Hsf Hlf]].
           apply Hmin with (la := LA tok)
                           (gamma := sym' :: syms')
             in Hsf.

           ++ unfold ptComplete in Hcom.
              destruct Hsf as [Hfi | Hfo].
              ** inv Hfi.
                 inv H0.
                 --- inv H4.
                     +++ assert (Hlkp : (@isLookaheadFor g)
                                          (LA tok)
                                          x
                                          []).
                         { unfold isLookaheadFor.
                           right.
                           split.
                           { constructor.
                             trivial.
                             constructor. }
                           { 
                           
                             


                     intros.
  destruct prefix; destruct suffix; simpl in *.
  - (* prefix and suffix are nil *)
    (* prove that they both derive nil? *)
  intros tbl g x prefix suffix gamma Htbl Hlkp.
  apply lookup_exists in Hlkp.
  destruct Hlkp as [laMap [Hsf Hlf]].
  pose proof Hsf as Hsf'.
  destruct Htbl as [Hmin Hcom].
  unfold ptMinimal in Hmin.
  unfold ptComplete in Hcom.
  apply Hmin with
      (la := peek (prefix ++ suffix)) (gamma := gamma) in Hsf.
  - destruct Hsf as [Hfirst | Hfollow].
    + inv Hfirst; intros.
      * destruct prefix; destruct suffix.
        -- simpl in *.

  
  induction prefix as [| pt pts].
  - induction suffix as [| st sts]; intros.
    + simpl in *.
      apply parseForest_correct with (g := g) in H1.
      * destruct H1 as [prefix [H3 H4]].
        assert (prefix = nil).
        { destruct prefix; trivial; inv H3. }
        subst.
        clear H3.
        apply lookup_exists in H2.
        destruct H2 as [laMap [Hsfind Hlfind]].
        destruct H.
        unfold ptMinimal in H.
        unfold ptComplete in H1.
        apply H with (la := EOF) (gamma := gamma') in Hsfind.
        -- destruct Hsfind.
           ++ apply eof_fprod in H2; inv H2.
              trivial.
           ++ destruct H2 as [Hnp Hfp].
              inv Hnp.
              inv H3.
              ** inv Hfp.
                 inv H5.
              





             
Lemma lookup_exists :
  forall x la tbl gamma,
    parseTableLookup x la tbl = Some gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.
Proof.
  intros.
  unfold parseTableLookup in H.
  destruct (StringMap.find x tbl) as [laMap |] eqn:Hsf.
  - exists laMap; split; trivial.
  - inv H.
Qed.

Lemma der_lookup :
   forall tbl g,
    isParseTableFor tbl g
    -> forall prefix suffix x gamma fuel f gamma',
       In (x, gamma) (productions g)
       -> parseForest tbl gamma (app prefix suffix) fuel =
          (Some f, suffix)
       -> parseTableLookup x (peek (app prefix suffix)) tbl =
          Some gamma'
       -> gamma = gamma'.
Proof.
  intros tbl g Htbl prefix.
  unfold isParseTableFor in Htbl.
  destruct Htbl as [Hmin Hcom].
  intros.
  apply lkp_ex in H1.
  destruct H1 as [laMap [Hsf Hlf]].
  pose proof Hsf.
  unfold ptMinimal in Hmin.
  apply Hmin with (la := peek (app prefix suffix))
                  (gamma := gamma') in Hsf.
  - destruct (peek (prefix ++ suffix)) eqn:Hpeek.
    + unfold ptComplete in Hcom.
      apply Hcom with (la := LA s) in Hsf.
      destruct Hsf as [laMap' [Hsf' Hlf']].
      rewrite H1 in Hsf'.
      inv Hsf'.
      rewrte 

  
  induction prefix as [| pt pts]; intros.
  - simpl in *.
    apply lkp_ex in H1.
    destruct H1 as [laMap [Hsf Hlf]].
    unfold ptMinimal in Hmin.
    unfold ptComplete in Hcom.
    apply Hmin with (la := peek suffix) (gamma := gamma')
      in Hsf.
    + unfold isLookaheadFor in Hsf.
      destruct Hsf as [Hfp | Hnp].
      * inv Hfp.
        inv H2.
        -- inv H3.
        rewrite <- H4 in Hlf.
        
    
  induction gamma as [| sym syms]; intros.
  - inv H0.
    simpl.
    unfold ptMinimal in Hmin.
    unfold parseTableLookup.
    destruct (StringMap.find x tbl) as [laMap |] eqn:Hsf.
    + destruct (LookaheadMap.find EOF laMap)
        as [gamma |] eqn:Hlf.
      * destruct gamma.
        -- trivial.
        -- eapply Hmin with (la := EOF) (gamma := gamma)
            in Hsf.
           ++ unfold Hsf.
j
    
    inv H0.
    destruct Htbl with (x := x) (la := EOF) (gamma := @nil symbol)
      as [Hmin Hcom].
    inv H0.
    simpl.
    apply Hcom.
    unfold isLookaheadFor.
    right.
    split.
    + constructor.
      * trivial.
      * constructor.
    + unfold parseTableLookup in Hmin.
      destruct (StringMap.find x tbl) as [laMap |] eqn:Hsf.
      * destruct (LookaheadMap.find EOF laMap) as [gamma |].
        -- destruct (list_eq_dec symbol_eq_dec 

    unfold parseTableLookup; unfold parseTableLookup in Hmin.
    destruct (StringMap.find x tbl) eqn:Hsfind.
    + destruct (LookaheadMap.find EOF t) eqn:Hlfind.
      * 
    
      



  unfold isParseTableFor in Htbl.
  destruct Htbl as [Hcom Hmin].
  destruct Hcom as [Hcomfi Hcomfo].
  unfold ptCompleteFirst in Hcomfi.
  unfold ptCompleteFollow in Hcomfo.
  induction trees as [| tr trs]; intros.
  - inv H0.
    simpl in *.
    inv H.
    inv H4.
    unfold parseTableMinimal in Hmin.
    apply Hcomfo with (y := EOF) in H2.
    + destruct H2 as [tMap [H2 H3]].
      unfold parseTableLookup.
      rewrite H2; rewrite H3.
      trivial.
    + constructor.
    + apply Hmin in H2.
      apply Hcomfo in H
      * destruct H2.
        -- inv H.
           inv H0.
           inv H1.
        -- destruct H0.
           unfold parseTableLookup.
           rewrite H; rewrite H3.
           trivial.
      * trivial.
    + constructor.
    + 



      
Lemma in_grammar_lookup_tbl :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma prefix suffix x fuel f,
      In (x, gamma) (productions g)
      -> parseForest tbl gamma (app prefix suffix) fuel =
         (Some f, suffix)
      -> parseTableLookup x (peek (app prefix suffix)) tbl =
         Some gamma.
Proof.
  intros tbl g Htbl gamma.
  intros.
  assert (H1 : exists (prefix' : list string),
               (app prefix' suffix) = (app prefix suffix)
               /\ (@derivesForest g) gamma prefix' f).
  { admit. }
  destruct H1 as [prefix' [H1 H2]].
  assert (prefix' = prefix).
  { admit. }
  subst.
  assert ((@derivesTree g) (NT x) prefix (Node x f)).
  { eapply derivesNT; eauto. }
  apply derives_exists in H3.

(* Ultimate goal *)
(*
  g : grammar
  tbl : parse_table
  Htbl : isParseTableFor tbl g
  s : string
  f : forest
  prefix, suffix : list string
  gamma : list symbol
  H3 : In (s, gamma) (productions g)
  fuel : nat
  H : parseForest tbl gamma (prefix ++ suffix) fuel =
      (Some f, suffix)
  gamma' : list symbol
  Hlkp : parseTableLookup s (peek (prefix ++ suffix)) tbl =
         Some gamma'
  f' : forest
  suffix' : list string
  Hpf : parseForest tbl gamma' (prefix ++ suffix) fuel =
        (Some f', suffix')
  ============================
  (Some (Node s f'), suffix') = (Some (Node s f), suffix)

 *)



(*

case 1 -- prefix == suffix == nil

In (x, gamma) (productions g)

parseForest gamma nil = (Some f, nil)
--> derivesForest gamma nil f

parseTableLookup x EOF = Some gamma'
--> we know that either EOF is in FIRST for (x, gamma')
    (can't be true), or that gamma' is nullable and 
    EOF is in FOLLOW for (x, gamma')
       
parseForest gamma' nil = (Some f', suffix')
--> suffix' = nil