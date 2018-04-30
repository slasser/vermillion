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

(* Generate induction scheme with /\ in the conclusion *)
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

             
Lemma lookup_exists' :
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

(* 
  g : grammar
  tbl : parse_table
  Htbl : isParseTableFor tbl g
  s : string
  f : forest
  prefix, suffix : list string
  Hmax : forall (pre' suf' : list string) (tree' : tree),
         (prefix ++ suffix)%list = (pre' ++ suf')%list ->
         derivesTree (NT s) pre' tree' -> Datatypes.length pre' <= Datatypes.length prefix
  gamma : list symbol
  H3 : In (s, gamma) (productions g)
  fuel : nat
  H : parseForest tbl gamma (prefix ++ suffix) fuel = (Some f, suffix)
  gamma' : list symbol
  Hlkp : parseTableLookup s (peek (prefix ++ suffix)) tbl = Some gamma'
  f' : forest
  suffix' : list string
  Hpf : parseForest tbl gamma' (prefix ++ suffix) fuel = (Some f', suffix')
  ============================
  (Some (Node s f'), suffix') = (Some (Node s f), suffix) 
*)

Lemma in_grammar_lookup_tbl :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma prefix suffix x tr f fuel,
      In (x, gamma) (productions g)
      -> derivesMaximalTree g (NT x) prefix suffix tr
      -> parseForest tbl gamma (prefix ++ suffix) fuel = (Some f, suffix)
      -> parseTableLookup x (peek (app prefix suffix)) tbl =
         Some gamma.
Proof.
  intros tbl g Htbl gamma.
  intros.
  destruct H0 as [Hder Hmax].
  destruct prefix eqn:Hpre; destruct suffix eqn:Hsuf;
  simpl in *.
  - (* pre and suf are nil *)
    inv Hder.
    inv H2.
    + 
    
    
  (* Ultimate goal *)
  (* 

   g : grammar
  tbl : parse_table
  Htbl : isParseTableFor tbl g
  s : string
  f : forest
  prefix, suffix : list string
  Hmax : forall (pre' suf' : list string) (tree' : tree),
         (prefix ++ suffix)%list = (pre' ++ suf')%list ->
         derivesTree (NT s) pre' tree' ->
         Datatypes.length pre' <= Datatypes.length prefix
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