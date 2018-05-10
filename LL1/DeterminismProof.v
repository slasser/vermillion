Require Import List Omega String.
Require Import Derivation Grammar Lemmas ParseTable Utils
        ParseTree LL1.Parser Lib.Tactics
        LL1.CorrectnessProof LL1.MonotonicityLemmas.
Import ListNotations.
Open Scope list_scope.


Inductive derivesProd {g : grammar} :
  nonterminal -> list symbol -> list string -> tree -> Prop :=
| derProd :
    forall x gamma tokens f,
      In (x, gamma) g.(productions)
      -> derivesGamma gamma tokens f
      -> derivesProd x gamma tokens (Node x f)
with derivesGamma {g : grammar} : 
       list symbol -> list string -> forest -> Prop :=
     | derivesFnil : derivesGamma [] [] Fnil
     | derivesFcons : 
         forall (hdSym : symbol)
                (prefix suffix : list string)
                (hdTree : tree)
                (tlSyms : list symbol)
                (tlTrees : forest),
           derivesSym hdSym prefix hdTree
         -> derivesGamma tlSyms suffix tlTrees
         -> derivesGamma (hdSym :: tlSyms) 
                         (prefix ++ suffix) 
                         (Fcons hdTree tlTrees)
with derivesSym {g : grammar} : 
       symbol -> list string -> tree -> Prop :=
     | derivesT : 
         forall (y : string),
           derivesSym (T y) [y] (Leaf y)
     | derivesNT : 
         forall (x : string) 
                (gamma : list symbol) 
                (tokens : list string) 
                tr,
           derivesProd x gamma tokens tr
           -> derivesSym (NT x) tokens tr.

Scheme derivesProd_mut_ind := Induction for derivesProd Sort Prop
  with derivesGamma_mut_ind := Induction for derivesGamma Sort Prop
  with derivesSym_mut_ind := Induction for derivesSym Sort Prop.


Lemma derivesSym_nil_nullable :
  forall tr g sym,
    (@derivesSym g) sym [] tr
    -> (@nullableSym g) sym.
 Proof.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall g sym,
                (@derivesSym g) sym [] tr
                -> (@nullableSym g) sym)
      (P0 := fun f =>
               forall g gamma,
                 (@derivesGamma g) gamma nil f
                 -> (@nullableGamma g) gamma).

  - intros g sym Hder.
    inv Hder.
    inv H.

  - intros g sym Hder.
    inv Hder.
    inv H.
    econstructor.
    econstructor.
    + eauto.
    + apply IHtr.
      auto.

  - intros g gamma Hder.
    inv Hder.
    constructor.

  - intros g gamma Hder.
    inv Hder.
    assert (prefix = nil).
    { destruct prefix; destruct suffix; try inv H; auto. }
    assert (suffix = nil).
    { destruct prefix; destruct suffix; try inv H; auto. }
    subst.
    clear H.
    inv H3.
    inv H.
    constructor.
    + apply IHtr.
      econstructor.
      econstructor; eauto.
    + apply IHtr0.
      auto.
 Qed.

 Lemma derivesGamma_nil_nullable :
  forall f g gamma,
    (@derivesGamma g) gamma [] f
    -> (@nullableGamma g) gamma.
 Proof.
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall g sym,
                (@derivesSym g) sym [] tr
                -> (@nullableSym g) sym)
      (P0 := fun f =>
               forall g gamma,
                 (@derivesGamma g) gamma nil f
                 -> (@nullableGamma g) gamma).

  - intros g sym Hder.
    inv Hder.
    inv H.

  - intros g sym Hder.
    inv Hder.
    inv H.
    econstructor.
    econstructor.
    + eauto.
    + apply IHf.
      auto.

  - intros g gamma Hder.
    inv Hder.
    constructor.

  - intros g gamma Hder.
    inv Hder.
    assert (prefix = nil).
    { destruct prefix; destruct suffix; try inv H; auto. }
    assert (suffix = nil).
    { destruct prefix; destruct suffix; try inv H; auto. }
    subst.
    clear H.
    inv H3.
    inv H.
    constructor.
    + apply IHf.
      econstructor.
      econstructor; eauto.
    + apply IHf0.
      auto.
 Qed.

 (* to do *)
 Lemma derivesGamma_cons_firstGamma :
   forall f g tok toks gamma,
     (@derivesGamma g) gamma (tok :: toks) f
    -> (@firstGamma g) (LA tok) gamma.
 Proof.
 Admitted.

 Fixpoint appF f f2 :=
   match f with
   | Fnil => f2
   | Fcons tr f' => Fcons tr (appF f' f2)
   end.

Lemma appF_nil_r : forall f,
    appF f Fnil = f.
Proof.
  induction f; simpl.
  - auto.
  - rewrite IHf. auto.
Qed.

Lemma appF_nil_l : forall f,
    appF Fnil f = f.
Proof.
  intros. simpl. auto.
Qed.

Fixpoint lengthF f :=
  match f with
  | Fnil => 0
  | Fcons t f' => 1 + lengthF f'
  end.

Lemma forest_length :
  forall g gamma word f,
    (@derivesGamma g) gamma word f
    -> List.length gamma = lengthF f.
Proof.
  induction gamma; intros.
  - inv H.
    simpl.
    auto.
  - inv H.
    simpl.
    apply eq_S.
    eapply IHgamma.
    eauto.
Qed.

Lemma lengths_contra :
  forall f tr f',
    ~ lengthF f = lengthF (appF f (Fcons tr f')).
Proof.
  induction f; unfold not; intros.
  - simpl in H.
    inv H.
  - unfold not in *.
    simpl in *.
    apply (IHf tr f').
    auto.
Qed.

Lemma lengths_contra_l :
  forall f f' tr,
    ~ lengthF f = lengthF (appF (Fcons tr f') f).
Proof.
  induction f; unfold not in *; intros.
  - simpl in H.
    inv H.
  - simpl in *.
Admitted.

Lemma appF_Fcons_not_Fnil :
  forall f f' tr,
    Fnil <> appF f (Fcons tr f').
Proof.
  destruct f; unfold not; intros; simpl in *.
  - inv H.
  - inv H.
Qed.

Lemma nullable_middle_sym :
  forall g xs ys sym,
    (@nullableGamma g) (xs ++ sym :: ys)
    -> (@nullableSym g) sym.
Proof.
  induction xs; intros.
  - simpl in H.
    inv H.
    auto.
  - eapply IHxs.
    inv H.
    eauto.
Qed.

Lemma gamma_with_terminal_not_nullable :
  forall g xs y zs,
    (@nullableGamma g) (xs ++ T y :: zs)
    -> False.
Proof.
  induction xs; intros.
  - simpl in H.
    inv H.
  - destruct a.
    + inv H.
    + inv H.
      eapply IHxs; eauto.
Qed.

Lemma nullable_split :
  forall g xs ys,
    (@nullableGamma g) (xs ++ ys)
    -> (@nullableGamma g) ys.
Proof.
  induction xs; intros.
  - auto.
  - inv H.
    eapply IHxs; eauto.
Qed.
  
Lemma no_first_follow_conflicts :
  forall tbl g,
    isParseTableFor tbl g
    -> forall la sym gamma,
      (@firstProd g) la sym gamma
      -> (@nullableProd g) sym gamma
      -> (@followProd g) la sym gamma
      -> False.
Proof.
  intros tbl g Htbl la sym gamma Hfi.
  destruct Htbl as [Hmin Hcom].
  induction Hfi using firstProd_mutual_ind with
      (P := fun la sym gamma
                (pf : (@firstProd g) la sym gamma) =>
              (@nullableProd g) sym gamma
              -> (@followProd g) la sym gamma
              -> False)
      (P0 := fun la gammaSuf
                 (pf : (@firstGamma g) la gammaSuf) =>
               forall sym gammaPre,
                 (@firstProd g) la sym (gammaPre ++ gammaSuf)
                 -> (@nullableProd g) sym (gammaPre ++ gammaSuf)
                 -> (@followProd g) la sym (gammaPre ++ gammaSuf)
                 -> False)
      (P1 := fun la sym (pf : (@firstSym g) la sym) =>
              (@nullableSym g) sym
              -> (@followSym g) la sym
              -> False).

  - intros Hnu Hfo.
    eapply IHHfi; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H in i.
      econstructor; eauto.
    + auto.
    + auto.

  - intros sym gammaSuf Hfi Hnu Hfo.
    eapply IHHfi.
    + inv Hnu.
      apply nullable_middle_sym in H0.
      auto.
    + destruct hd.
      * inv Hnu.
        apply gamma_with_terminal_not_nullable in H0.
        inv H0.
      * inv Hfo.
        inv Hnu.
        eapply FoLeft; eauto.
        assert (NT n :: tl = [NT n] ++ tl) by auto.
        rewrite H1 in H3.
        rewrite app_assoc in H3.
        eapply nullable_split in H3.
        auto.        

  - intros sym gammaPre Hfi Hnu Hfo.
    eapply IHHfi.
    + assert (NT x :: tl = [NT x] ++ tl) by auto.
      rewrite H in Hfi.
      rewrite app_assoc in Hfi.
      eauto.
    + rewrite <- app_assoc.
      simpl.
      auto.
    + rewrite <- app_assoc.
      simpl.
      auto.

  - intros Hnu Hfo.
    inv Hnu.
    inv H.

  - intros Hnu Hfo.
    inv Hnu.
    inv H.
    assert (Hlk : (@isLookaheadFor g) la (NT x) gamma).
    { unfold isLookaheadFor.
      left.
      auto. }
    assert (Hlk' : (@isLookaheadFor g) la (NT x) ys).
    { unfold isLookaheadFor.
      right.
      split.
      { constructor; auto. }
      { constructor; auto. }}
    unfold ptComplete in Hcom.
    apply Hcom in Hlk; apply Hcom in Hlk'.
    destruct Hlk as [laMap [Hsf Hlf]].
    destruct Hlk' as [laMap' [Hsf' Hlf']].
    assert (gamma = ys) by congruence.
    subst.
    apply IHHfi.
    + constructor; auto.
    + constructor; auto.
Qed.

Lemma firstGamma_split :
  forall g la xs ys,
    (@firstGamma g) la xs
    -> (@firstGamma g) la (xs ++ ys).
Proof.
  induction xs; intros.
  - inv H.
  - inv H.
    + constructor; auto.
    + eapply FiGammaTl; eauto.
Qed.

Lemma derives_app :
  forall g gPre gSuf wPre wSuf fPre fSuf,
    (@derivesGamma g) gPre wPre fPre
    -> (@derivesGamma g) gSuf wSuf fSuf
    -> (@derivesGamma g) (gPre ++ gSuf)
                         (wPre ++ wSuf)
                         (appF fPre fSuf).
Proof.
  induction gPre; intros; simpl in *.
  - inv H.
    auto.
  - inv H.
    simpl.
    rewrite <- app_assoc.
    constructor.
    + auto.
    + apply IHgPre; auto.
Qed.

Lemma last_case :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sufGamma preGamma x x2 word f f',
      In (x, preGamma ++ NT x2 :: sufGamma) (productions g)
      -> (@derivesGamma g) (NT x2 :: sufGamma) word f
      -> (@derivesGamma g) (NT x2 :: sufGamma) word f'
      -> f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction sufGamma as [| sym syms].
  
Abort.

Lemma derivesSym_det : 
  forall tbl g,
    isParseTableFor tbl g
    -> forall f f' x pre gamma word,
      In (x, pre ++ gamma) (productions g)
      -> (@derivesGamma g) gamma word f
      -> (@derivesGamma g) gamma word f'
      -> f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr').
  - intros tr' sym word Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym word Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    assert (gamma = gamma0) by admit.
    subst.
    erewrite IHf; eauto.
    assert (gamma0 = [] ++ gamma0) by auto.
    rewrite H1 in H.
    eauto.

  - intros f' x pre gamma word Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    auto.

  - intros f' x pre gamma word Hin Hder Hder'.
    inv Hder; inv Hder'.
    destruct tlSyms.
    + inv H6; inv H4.
      repeat rewrite app_nil_r in *.
      subst.
      erewrite IHf; eauto.
    + 
      
    
    destruct hdSym as [y | x2].
    + inv H2; inv H3.
      inv H1.
      erewrite IHf0; auto.
      * assert (T y :: tlSyms = [T y] ++ tlSyms) by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.
      * eauto.
      * auto.
    + revert Hin.
      revert pre.
      revert 
      * inv H6.
        inv H4.
        repeat rewrite app_nil_r in *.
        subst.
        erewrite IHf; eauto.
      * 
      

          

      
(* BEST ATTEMPT SO FAR *)

Lemma derivesSym_det :
  forall tbl g tr sym word,
    isParseTableFor tbl g
    -> (@derivesSym g) sym word tr
    -> forall tr',
        (@derivesSym g) sym word tr'
        -> tr = tr'.
Proof.
  intros tbl g tr sym word Htbl Hder.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction Hder using derivesSym_mut_ind with
      (P := fun x gamma word tr
                (pf : (@derivesProd g) x gamma word tr) =>
                 forall tr',
                   (@derivesProd g) x gamma word tr'
                   -> tr = tr')
      (P0 := fun gamma word f
                 (pf : (@derivesGamma g) gamma word f) =>
               forall x preGamma f',
                 In (x, preGamma ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').
  - intros tr' Hderp.
    inv Hderp.
    erewrite IHHder; eauto.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in i.
    eauto.
    
  - intros x preGamma f' Hin Hderg.
    inv Hderg.
    auto.

  - intros x preGamma f' Hin Hderg.
    pose proof Hderg as Hderg'.
    inv Hderg.
    destruct hdSym as [tName | ntName].
    + inv H2.
      inv Hder.
      inv H1.
      eapply IHHder0 in H4; subst; auto.
      assert (T tName :: tlSyms = [T tName] ++ tlSyms) by auto.
      rewrite H in Hin.
      assert (preGamma ++ [T tName] ++ tlSyms =
              (preGamma ++ [T tName]) ++ tlSyms).
      { rewrite app_assoc. auto. }
      rewrite H0 in Hin.
      eauto.

    + assert (prefix = prefix0).
      { (* Maybe I should be doing induction here? *)
        destruct prefix as [| ptok ptoks] eqn:Hpre;
          destruct prefix0 as [| ptok' ptoks'] eqn:Hpre';
          intros; simpl in *.
        
        - auto.
          
        - (* first / follow *)
          exfalso.
          inv Hder.
          inv H2.
          assert (Hlk : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma).
          { unfold isLookaheadFor.
            right.
            inv H0.
            split.
            { constructor; auto.
              apply derivesGamma_nil_nullable in H2.
              auto. }
            { constructor; auto.
              eapply FoRight; eauto.
              apply derivesGamma_cons_firstGamma in d.
              auto. }}
          assert (Hlk' : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma0).
          { unfold isLookaheadFor.
            left.
            inv H1.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H2.
            auto. }
          unfold ptComplete in Hcom.
          apply Hcom in Hlk; apply Hcom in Hlk'.
          destruct Hlk as [laMap [Hsf Hlf]].
          destruct Hlk' as [laMap' [Hsf' Hlf']].
          assert (gamma = gamma0) by congruence.
          subst.
          inv H0; inv H1.
          assert ((@firstProd g) (LA ptok') (NT ntName) gamma0).
          { constructor; auto.
            apply derivesGamma_cons_firstGamma in H3.
            auto. }
          assert ((@nullableProd g) (NT ntName) gamma0).
          { constructor; auto.
            apply derivesGamma_nil_nullable in H2.
            auto. }
          assert ((@followProd g) (LA ptok') (NT ntName) gamma0).
          { constructor; auto.
            econstructor; eauto.
            apply derivesGamma_cons_firstGamma in d.
            auto. }
          eapply no_first_follow_conflicts; eauto.
          
        - (* another conflict *)
          exfalso.
          inv Hder.
          inv H2.
          assert (Hlk : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma0).
          { unfold isLookaheadFor.
            right.
            inv H1.
            split.
            { constructor; auto.
              apply derivesGamma_nil_nullable in H2.
              auto. }
            { constructor; auto.
              eapply FoRight; eauto.
              apply derivesGamma_cons_firstGamma in H4.
              auto. }}
          assert (Hlk' : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma).
          { unfold isLookaheadFor.
            left.
            inv H0.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H2.
            auto. }
          unfold ptComplete in Hcom.
          apply Hcom in Hlk; apply Hcom in Hlk'.
          destruct Hlk as [laMap [Hsf Hlf]].
          destruct Hlk' as [laMap' [Hsf' Hlf']].
          assert (gamma = gamma0) by congruence.
          subst.
          inv H0; inv H1.
          assert ((@firstProd g) (LA ptok) (NT ntName) gamma0).
          { constructor; auto.
            apply derivesGamma_cons_firstGamma in H2.
            auto. }
          assert ((@nullableProd g) (NT ntName) gamma0).
          { constructor; auto.
            apply derivesGamma_nil_nullable in H3.
            auto. }
          assert ((@followProd g) (LA ptok) (NT ntName) gamma0).
          { constructor; auto.
            econstructor; eauto.
            apply derivesGamma_cons_firstGamma in H4.
            auto. }
          eapply no_first_follow_conflicts; eauto.
          
        - inv H1.
          inv Hder; inv H2.
          inv H0; inv H1.
          assert (gamma = gamma0) by admit.
          subst.
          admit. }

      assert (suffix0 = suffix) by admit.
      subst.
      erewrite IHHder; erewrite IHHder0; eauto.
      * assert (NT ntName :: tlSyms =
                [NT ntName] ++ tlSyms) by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.
      * assert (NT ntName :: tlSyms =
                [NT ntName] ++ tlSyms) by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.

  - intros tr' Hder.
    inv Hder.
    auto.
    
  - intros tr' Hder.
    inv Hder.
    inv d; inv H0.
    pose proof H1 as Hder.
    pose proof H3 as Hder'.
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF (NT x) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT x) gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite IHHder; eauto.
      constructor; auto.

    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) (NT x) gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) (NT x) gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      apply IHHder; constructor; auto.
Admitted.
    

            
          (*      
Lemma last_case :
  forall tbl g tr f x preGamma ntName tlSyms sufGamma,
    isParseTableFor tbl g
    -> (forall tr' sym word,
           (@derivesSym g) sym word tr
           -> (@derivesSym g) sym word tr'
           -> tr = tr')
    -> (forall f' x preGamma gamma sufGamma word,
           In (x, preGamma ++ gamma ++ sufGamma)
              (productions g)
           -> (@derivesGamma g) gamma word f
           -> (@derivesGamma g) gamma word f'
           -> f = f')
    -> In (x, preGamma ++ (NT ntName :: tlSyms) ++ sufGamma)
          (productions g)
    -> forall prefix suffix prefix0 suffix0 hdTree tlTrees,
        (@derivesSym g) (NT ntName) prefix tr
        -> (@derivesGamma g) tlSyms suffix f
        -> (@derivesSym g) (NT ntName) prefix0 hdTree
        -> (@derivesGamma g) tlSyms suffix0 tlTrees
        -> prefix0 ++ suffix0 = prefix ++ suffix
        -> Fcons tr f = Fcons hdTree tlTrees.
Proof.
  intros tbl g tr f x preGamma ntName tlSyms sufGamma
         Htbl IHtr IHf Hin.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction prefix as [| ptok ptoks].

  - intros suffix prefix0 suffix0 hdTree tlTrees
           Hders Hderg Hders' Hderg' Happ.
    simpl in *.
    destruct prefix0 as [| ptok' ptoks']; simpl in *.
    +  subst.
       apply IHtr in Hders'; subst; auto.
       eapply IHf in Hderg'; subst; eauto.
       assert (NT ntName :: tlSyms = [NT ntName] ++ tlSyms) by auto.
       rewrite app_comm_cons in Hin.
       repeat rewrite H in Hin.
       assert (preGamma ++ [NT ntName] ++ tlSyms =
               (preGamma ++ [NT ntName]) ++ tlSyms).
       { rewrite app_assoc; auto. }
       rewrite app_assoc in Hin.
       rewrite H0 in Hin.
       rewrite <- app_assoc in Hin.
       eauto.
    + exfalso.
      inv Hders.
      inv Hders'.
      assert (Hlk : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma).
       { unfold isLookaheadFor.
         right.
         inv H0.
         split.
         { constructor; auto.
           apply derivesGamma_nil_nullable in H2.
           auto. }
         { constructor; auto.
           eapply FoRight; eauto.
           apply derivesGamma_cons_firstGamma in Hderg.
           apply firstGamma_split.
           auto. }}
       assert (Hlk' : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma0).
       { unfold isLookaheadFor.
         left.
         inv H1.
         constructor; auto.
         apply derivesGamma_cons_firstGamma in H2.
         auto. }
       unfold ptComplete in Hcom.
       apply Hcom in Hlk; apply Hcom in Hlk'.
       destruct Hlk as [laMap [Hsf Hlf]].
       destruct Hlk' as [laMap' [Hsf' Hlf']].
       assert (gamma = gamma0) by congruence.
       subst.
       inv H0; inv H1.
       assert ((@firstProd g) (LA ptok') (NT ntName) gamma0).
       { constructor; auto.
         apply derivesGamma_cons_firstGamma in H3.
         auto. }
       assert ((@nullableProd g) (NT ntName) gamma0).
       { constructor; auto.
         apply derivesGamma_nil_nullable in H2.
         auto. }
       assert ((@followProd g) (LA ptok') (NT ntName) gamma0).
       { constructor; auto.
         econstructor; eauto.
         apply derivesGamma_cons_firstGamma in Hderg.
         apply firstGamma_split.
         auto. }
       eapply no_first_follow_conflicts; eauto.
    (* Whoa, it worked! *)

  - intros suffix prefix0 suffix0 hdTree tlTrees
           Hders Hderg Hders' Hderg' Happ.
    destruct prefix0 as [| ptok' ptoks']; simpl in *.
    + exfalso.
      inv Hders'.
      inv Hders.
      assert (Hlk : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma).
      { unfold isLookaheadFor.
        right.
        inv H0.
        split.
        { constructor; auto.
          apply derivesGamma_nil_nullable in H2.
          auto. }
        { constructor; auto.
          eapply FoRight; eauto.
          apply derivesGamma_cons_firstGamma in Hderg'.
          apply firstGamma_split.
          auto. }}
           assert (Hlk' : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma0).
           { unfold isLookaheadFor.
             left.
             inv H1.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H2.
             auto. }
           unfold ptComplete in Hcom.
           apply Hcom in Hlk; apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (gamma = gamma0) by congruence.
           subst.
           inv H0; inv H1.
           assert ((@firstProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_cons_firstGamma in H3.
             auto. }
           assert ((@nullableProd g) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_nil_nullable in H2.
             auto. }
           assert ((@followProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             econstructor; eauto.
             apply derivesGamma_cons_firstGamma in Hderg'.
             apply firstGamma_split.
             auto. }
           eapply no_first_follow_conflicts; eauto.
    + inv Happ.
*)      


(* putting some padding on both sides of gamma *)
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr')
      (P0 := fun f =>
               forall f' x preGamma gamma sufGamma word,
                 In (x, preGamma ++ gamma ++ sufGamma)
                    (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').

  - intros tr' sym word Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym word Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    rename s into x.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    destruct word as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF (NT x) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT x) gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      assert (gamma0 = [] ++ gamma0 ++ []).
      { rewrite app_nil_r; auto. }
      rewrite H1 in H.
      eauto.

    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) (NT x) gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) (NT x) gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      assert (gamma0 = [] ++ gamma0 ++ []).
      { rewrite app_nil_r; auto. }
      rewrite H1 in H.
      eauto.

  - intros f' x preGamma gamma sufGamma word Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    auto.

  - intros f' x preGamma gamma sufGamma word Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    destruct hdSym as [tName | ntName].
    + inv H2.
      inv H3.
      inv H1.
      eapply IHtr0 in H6; subst; auto.
      assert (T tName :: tlSyms = [T tName] ++ tlSyms) by auto.
      rewrite H in Hin.
      assert (preGamma ++ [T tName] ++ tlSyms =
              (preGamma ++ [T tName]) ++ tlSyms).
      { rewrite app_assoc. auto. }
      rewrite app_assoc in Hin.
      rewrite H0 in Hin.
      rewrite <- app_assoc in Hin.
      eauto.
    + destruct prefix as [| ptok ptoks].
      * simpl in *.
        subst.
        destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- apply IHtr in H2; subst; auto.
           eapply IHtr0 in H6; subst; eauto.
           assert (NT ntName :: tlSyms = [NT ntName] ++ tlSyms) by auto.
           rewrite app_comm_cons in Hin.
           repeat rewrite H in Hin.
           assert (preGamma ++ [NT ntName] ++ tlSyms =
                   (preGamma ++ [NT ntName]) ++ tlSyms).
           { rewrite app_assoc; auto. }
           rewrite app_assoc in Hin.
           rewrite H0 in Hin.
           rewrite <- app_assoc in Hin.
           eauto.
        -- exfalso.
           inv H3.
           inv H2.
           assert (Hlk : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma).
           { unfold isLookaheadFor.
             right.
             inv H0.
             split.
             { constructor; auto.
               apply derivesGamma_nil_nullable in H2.
               auto. }
             { constructor; auto.
               eapply FoRight; eauto.
               apply derivesGamma_cons_firstGamma in H4.
               apply firstGamma_split.
               auto. }}
           assert (Hlk' : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma0).
           { unfold isLookaheadFor.
             left.
             inv H1.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H2.
             auto. }
           unfold ptComplete in Hcom.
           apply Hcom in Hlk; apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (gamma = gamma0) by congruence.
           subst.
           inv H0; inv H1.
           assert ((@firstProd g) (LA ptok') (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_cons_firstGamma in H3.
             auto. }
           assert ((@nullableProd g) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_nil_nullable in H2.
             auto. }
           assert ((@followProd g) (LA ptok') (NT ntName) gamma0).
           { constructor; auto.
             econstructor; eauto.
             apply derivesGamma_cons_firstGamma in H4.
             apply firstGamma_split.
             auto. }
           eapply no_first_follow_conflicts; eauto.
           (* Whoa, it worked! *)

      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- exfalso.
           inv H2.
           inv H3.
           assert (Hlk : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma).
           { unfold isLookaheadFor.
             right.
             inv H0.
             split.
             { constructor; auto.
               apply derivesGamma_nil_nullable in H2.
               auto. }
             { constructor; auto.
               eapply FoRight; eauto.
               apply derivesGamma_cons_firstGamma in H6.
               apply firstGamma_split.
               auto. }}
           assert (Hlk' : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma0).
           { unfold isLookaheadFor.
             left.
             inv H1.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H2.
             auto. }
           unfold ptComplete in Hcom.
           apply Hcom in Hlk; apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (gamma = gamma0) by congruence.
           subst.
           inv H0; inv H1.
           assert ((@firstProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_cons_firstGamma in H3.
             auto. }
           assert ((@nullableProd g) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_nil_nullable in H2.
             auto. }
           assert ((@followProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             econstructor; eauto.
             apply derivesGamma_cons_firstGamma in H6.
             apply firstGamma_split.
             auto. }
           eapply no_first_follow_conflicts; eauto.

        -- inv H1.
           

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr')
      (P0 := fun sufF =>
               forall sufF' x preGamma sufGamma sufWord,
                 In (x, preGamma ++ sufGamma) (productions g)
                 -> (@derivesGamma g) sufGamma sufWord
                                      sufF
                 -> (@derivesGamma g) sufGamma sufWord
                                      sufF'
                 -> sufF = sufF').

  - intros tr' sym word Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym word Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    rename s into x.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    destruct word as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF (NT x) gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF (NT x) gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      assert (gamma0 = [] ++ gamma0).
      { rewrite app_nil_l. auto. }
      rewrite H1 in H.
      eauto.

    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) (NT x) gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) (NT x) gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      assert (gamma0 = [] ++ gamma0) by auto.
      rewrite H1 in H.
      eauto.

  - intros preF' x preGamma sufGamma preWord Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    auto.

  - intros sufF' x preGamma sufGamma sufWord Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    destruct hdSym as [tName | ntName].
    + inv H2.
      inv H3.
      inv H1.
      eapply IHtr0 in H6; subst; eauto.
      assert (T tName :: tlSyms = [T tName] ++ tlSyms) by auto.
      rewrite H in Hin.
      rewrite app_assoc in Hin.
      eauto.
    + destruct prefix as [| ptok ptoks].
      * simpl in *.
        subst.
        destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- apply IHtr in H2; subst; auto.
           eapply IHtr0 in H6; subst; eauto.
           assert (NT ntName :: tlSyms = [NT ntName] ++ tlSyms) by auto.
      rewrite H in Hin.
      rewrite app_assoc in Hin.
      eauto.
        -- exfalso.
           pose proof H3 as Hder.
           inv H3.
           inv H2.
           assert (Hlk : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma).
           { unfold isLookaheadFor.
             right.
             inv H0.
             split.
             { constructor; auto.
               apply derivesGamma_nil_nullable in H2.
               auto. }
             { constructor; auto.
               eapply FoRight; eauto.
               apply derivesGamma_cons_firstGamma in H4.
               auto. }}
           assert (Hlk' : (@isLookaheadFor g) (LA ptok') (NT ntName) gamma0).
           { unfold isLookaheadFor.
             left.
             inv H1.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H2.
             auto. }
           unfold ptComplete in Hcom.
           apply Hcom in Hlk; apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (gamma = gamma0) by congruence.
           subst.
           inv H0; inv H1.
           assert ((@firstProd g) (LA ptok') (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_cons_firstGamma in H3.
             auto. }
           assert ((@nullableProd g) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_nil_nullable in H2.
             auto. }
           assert ((@followProd g) (LA ptok') (NT ntName) gamma0).
           { constructor; auto.
             econstructor; eauto.
             apply derivesGamma_cons_firstGamma in H4.
             auto. }
           eapply no_first_follow_conflicts; eauto.
           (* Whoa, it worked! *)

      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- exfalso.
           inv H2.
           inv H3.
           assert (Hlk : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma).
           { unfold isLookaheadFor.
             right.
             inv H0.
             split.
             { constructor; auto.
               apply derivesGamma_nil_nullable in H2.
               auto. }
             { constructor; auto.
               eapply FoRight; eauto.
               apply derivesGamma_cons_firstGamma in H6.
               auto. }}
           assert (Hlk' : (@isLookaheadFor g) (LA ptok) (NT ntName) gamma0).
           { unfold isLookaheadFor.
             left.
             inv H1.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H2.
             auto. }
           unfold ptComplete in Hcom.
           apply Hcom in Hlk; apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (gamma = gamma0) by congruence.
           subst.
           inv H0; inv H1.
           assert ((@firstProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_cons_firstGamma in H3.
             auto. }
           assert ((@nullableProd g) (NT ntName) gamma0).
           { constructor; auto.
             apply derivesGamma_nil_nullable in H2.
             auto. }
           assert ((@followProd g) (LA ptok) (NT ntName) gamma0).
           { constructor; auto.
             econstructor; eauto.
             apply derivesGamma_cons_firstGamma in H6.
             auto. }
           eapply no_first_follow_conflicts; eauto.

        -- inv H1.
           
              
           
        
        
               








              
             assert (Hder : (@derivesGamma g) (NT ntName :: tlSyms)
                                            (ptok' :: ptoks')
                                            (Fcons tr f)).
           { assert (ptok' :: ptoks' =
                     [] ++ (ptok' :: ptoks'))
               by auto.
             rewrite H.
             econstructor; eauto. }
           assert (Hder' : (@derivesGamma g) (NT ntName :: tlSyms)
                                             (ptok' :: ptoks')
                                             (Fcons hdTree tlTrees)).
           { assert (ptok' :: ptoks' =
                     ptok' :: ptoks' ++ []).
             { rewrite app_nil_r. auto. }
             rewrite H.
             rewrite app_comm_cons.
             econstructor; eauto. }
           
Abort.      
      

Fixpoint inF tr f :=
  match f with
  | Fnil => False
  | Fcons tr' f' => tr = tr' \/ inF tr f'
  end.

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_nested_ind with
      (Q := fun preF =>
              forall preF' x preGamma sufGamma
                     preWord sufWord
                     sufF,
                In (x, preGamma ++ sufGamma) (productions g)
                -> (@derivesGamma g) preGamma preWord preF
                -> (@derivesGamma g) preGamma preWord preF'
                -> (@derivesGamma g) sufGamma sufWord sufF
                -> preF = preF').

Fixpoint inF tr f :=
  match f with
  | Fnil => False
  | Fcons tr' f' => tr = tr' \/ inF tr f'
  end.

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr')
      (P0 := fun f =>
               forall tr tr' sym,
                 
                      
                 In (x, gamma) (productions g)
                 -> (@derivesGamma g) gamma word (appF fPre f)
                 -> (@derivesGamma g) gamma word (appF fPre f')
                 -> f = f').



Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr')
      (P0 := fun sufF =>
               forall sufF' preF x gamma word,
                 In (x, gamma) (productions g)
                 -> (@derivesGamma g) gamma word
                                      (appF preF sufF)
                 -> (@derivesGamma g) gamma word
                                      (appF preF sufF')
                 -> sufF = sufF').

  - intros tr' sym word Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym word Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    rename s into x.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    destruct word as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      * assert (f = appF Fnil f) by auto.
        rewrite H1 in H7.
        eauto. 
      * simpl. auto.
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); eauto.
      * assert (f = appF Fnil f) by auto.
        rewrite H1 in H7.
        eauto. 
      * simpl. auto.

  - intros sufF' preF x gamma word
           Hin Hder Hder'.
    rewrite appF_nil_r in Hder.
    destruct sufF'.
    + auto.
    + apply forest_length in Hder.
      apply forest_length in Hder'.
      rewrite Hder in Hder'.
      apply lengths_contra in Hder'.
      inv Hder'.

  - intros sufF' preF x gamma word Hin Hder Hder'.
    assert (appF preF (Fcons tr f) =
            appF preF (appF (Fcons tr Fnil) f)) by auto.
    rewrite H in Hder.
    clear H.
    rewrite app
    inv Hder.
    + apply appF_Fcons_not_Fnil in H2.
      inv H2.
    + inv Hder'.
      destruct hdSym as [tName | ntName].
      * inv H0.
        inv H6.
        inv H4.
        
        destruct f
        assert (appF preF (Fcons tr f) =
                appF preF (appF (Fcons tr Fnil) f)).
        { auto. }
        rewrite H0 in H.
        
    
    

    
  - intros sufF' x preGamma sufGamma preWord sufWord preF
           Hin Hderp Hders Hders'.
    simpl in *.
    inv Hders.
    inv Hders'.
    destruct hdSym as [tName | ntName].
    + inv H3.
      inv H2.
      inv H1.
      eapply IHtr0 in H6; subst; auto.
      * assert (T tName :: tlSyms = [T tName] ++ tlSyms)
          by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.
      * eapply derives_app.
        -- eauto.
        -- repeat econstructor.
    + destruct prefix as [| ptok ptoks]; simpl in *.
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- subst.
           erewrite IHtr; eauto.
           erewrite IHtr0; auto.
           ++ assert (NT ntName :: tlSyms =
                      [NT ntName] ++ tlSyms) by auto.
              rewrite H in Hin.
              rewrite app_assoc in Hin.
              eauto.
           ++ eapply derives_app.
              ** eauto.
              ** econstructor.
                 eauto.
                 econstructor.
           ++ eauto.
           ++ auto.
        -- destruct suffix as [| stok stoks].
           ++ inv H1.
           ++ inv H1.

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym word,
                (@derivesSym g) sym word tr
                -> (@derivesSym g) sym word tr'
                -> tr = tr')
      (P0 := fun sufF =>
               forall sufF' x preGamma sufGamma
                      preWord sufWord preF,
                 In (x, gamma) (productions g)
                 -> (@derivesGamma g) preGamma preWord preF
                 -> (@derivesGamma g) sufGamma sufWord sufF
                 -> (@derivesGamma g) sufGamma sufWord sufF'
                 -> sufF = sufF').

  - intros tr' sym word Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym word Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    rename s into x.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    destruct word as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); auto.
      * assert (gamma0 = nil ++ gamma0) by auto.
        rewrite H1 in H.
        eauto.
      * econstructor. 
      * eauto.
      * eauto. 
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); auto.
      * assert (gamma0 = nil ++ gamma0) by auto.
        rewrite H1 in H.
        eauto.
      * econstructor. 
      * eauto.
      * auto.

  - intros sufF' x preGamma sufGamma preWord sufWord preF
           Hin Hderp Hders Hders'.
    inv Hders.
    inv Hders'.
    auto.

  - intros sufF' x preGamma sufGamma preWord sufWord preF
           Hin Hderp Hders Hders'.
    simpl in *.
    inv Hders.
    inv Hders'.
    destruct hdSym as [tName | ntName].
    + inv H3.
      inv H2.
      inv H1.
      eapply IHtr0 in H6; subst; auto.
      * assert (T tName :: tlSyms = [T tName] ++ tlSyms)
          by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.
      * eapply derives_app.
        -- eauto.
        -- repeat econstructor.
    + destruct prefix as [| ptok ptoks]; simpl in *.
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- subst.
           erewrite IHtr; eauto.
           erewrite IHtr0; auto.
           ++ assert (NT ntName :: tlSyms =
                      [NT ntName] ++ tlSyms) by auto.
              rewrite H in Hin.
              rewrite app_assoc in Hin.
              eauto.
           ++ eapply derives_app.
              ** eauto.
              ** econstructor.
                 eauto.
                 econstructor.
           ++ eauto.
           ++ auto.
        -- destruct suffix as [| stok stoks].
           ++ inv H1.
           ++ inv H1.
              
    

              
(* try induction on derives *)
Lemma derivesSym_det :
  forall tbl g sym word tr,
    isParseTableFor tbl g
    -> (@derivesSym g) sym word tr
    -> forall tr',
        (@derivesSym g) sym word tr'
        -> tr = tr'.
Proof.
  intros tbl g sym word tr Htbl Hder.
  induction Hder using derivesSym_mutual_ind with
      (P := fun x gamma word tr
                (pf : (@derivesProd g) x gamma word tr) =>
              forall tr',
                (@derivesProd g) x gamma word tr'
                -> tr = tr')
      (P0 := fun sym word tr
                 (pf : (@derivesSym g) sym word tr) =>
               forall tr',
                 (@derivesSym g) sym word tr'
                 -> tr = tr')
      (P1 := fun gSuf wSuf fSuf
                 (pf : (@derivesGamma g) gSuf wSuf fSuf) =>
               forall x gPre wPre fPre fSuf',
                 In (x, gPre ++ gSuf) (productions g)
                 -> (@derivesGamma g) (gPre ++ gSuf)
                                      (wPre ++ wSuf)
                                      (appF fPre fSuf)
                 -> (@derivesGamma g) (gPre ++ gSuf)
                                      (wPre ++ wSuf)
                                      (appF fPre fSuf')
                 -> fSuf = fSuf').
      
  - intros tr' Hder.
    inv Hder.
    erewrite IHHder; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H1 in i.
      eauto.
    + simpl.
      assert (tokens = [] ++ tokens) by auto.
      rewrite H1 in d.
      assert (f = appF Fnil f) by auto.
      rewrite H2 in d.
      eauto.
    + simpl.
      auto.

  - intros tr' Hder.
    inv Hder.
    auto.

  - intros tr' Hder.
    inv Hder.
    apply IHHder; clear IHHder.
    (* prove gamma = gamma0 *)
    destruct Htbl as [Hmin Hcom].
    inv d; inv H0.
    pose proof H1 as Hder.
    pose proof H3 as Hder'.
    destruct tokens as [| tok toks].
    + constructor; auto.
      apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      auto.

    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      constructor; auto.

  - intros x gPre wPre fPre fSuf' Hin Hder Hder'.
    repeat rewrite app_nil_r in *.
    rewrite appF_nil_r in Hder.
    destruct fSuf'.
    + auto.
    + apply forest_length in Hder.
      apply forest_length in Hder'.
      rewrite Hder in Hder'.
      apply lengths_contra in Hder'.
      inv Hder'.

  - intros x gPre xPre fPre fSuf' Hin Hder1 Hder2.
    
     
      
    


Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym tokens,
      (@derivesSym g) sym tokens tr
      -> (@derivesSym g) sym tokens tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym tokens,
                (@derivesSym g) sym tokens tr
                -> (@derivesSym g) sym tokens tr'
                -> tr = tr')
      (P0 := fun fSuf =>
               forall fSuf' fPre x gPre gSuf wPre wSuf,
                 In (x, gPre ++ gSuf) (productions g)
                 -> (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf wSuf fSuf'
                 -> fSuf = fSuf').

  - intros tr' sym tokens Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym tokens Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    rename s into x.
    destruct Htbl as [Hmin Hcom].
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); auto.
      * assert (nil ++ gamma0 = gamma0) by apply app_nil_l.
        rewrite <- H1 in H.
        eauto.
      * econstructor.
      * eauto.
      * auto.
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite (IHtr f0); auto.
      * assert (nil ++ gamma0 = gamma0) by apply app_nil_l.
        rewrite <- H1 in H.
        eauto.
      * econstructor.
      * eauto.
      * auto.

  - intros fSuf' fPre x gPre gSuf wPre wSuf
           Hin HderPre HderSuf HderSuf'.
    inv HderSuf.
    inv HderSuf'.
    auto.

  - intros fSuf' fPre x gPre gSuf wPre wSuf
           Hin Hderp Hders Hders'.
    inv Hders; inv Hders'.
    destruct hdSym as [tName | ntName].
    + inv H3; inv H2.
      inv H1.
      eapply IHtr0 in H6; auto.
      * subst.
        auto.
      * assert (T tName :: tlSyms = [T tName] ++ tlSyms)
          by auto.
        rewrite H in Hin.
        rewrite app_assoc in Hin.
        eauto.
      * eapply derives_app; eauto; repeat constructor.
    + destruct prefix as [| ptok ptoks].
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- subst.
           apply IHtr in H2; auto.
           eapply IHtr0 in H6; auto.
           ++ subst.
              auto.
           ++ assert (NT ntName :: tlSyms =
                      [NT ntName] ++ tlSyms) by auto.
              rewrite H in Hin.
              rewrite app_assoc in Hin.
              eauto.
           ++ eapply derives_app; eauto.
              econstructor.
              eauto.
              constructor.
        -- destruct suffix as [| stok stoks].
           ++ inv H1.
           ++ inv H1.
              (* first/follow conflict *)
              exfalso.
              








              
              destruct suffix0 as [| stok' stoks']; simpl in *.
              ** rewrite app_nil_r in *.
                 assert ((@derivesGamma g) (NT ntName :: tlSyms)
                                           (stok :: ptoks')
                                           (Fcons hdTree tlTrees)).
                 { assert (stok :: ptoks' =
                           stok :: ptoks' ++ []).
                   { rewrite app_nil_r.
                     auto. }
                   rewrite H.
                   eapply derivesFcons with
                       (prefix := stok :: ptoks')
                       (suffix := nil); auto. }
                 assert ((@derivesGamma g) (NT ntName :: tlSyms)
                                           (stok :: ptoks')
                                           (Fcons tr f)).
                 { assert (stok :: ptoks' =
                           [] ++ stok :: ptoks') by auto.
                   rewrite H0.
                   eapply derivesFcons with
                       (prefix := nil)
                       (suffix := stok :: ptoks'); auto. }
                 apply (derives_app g [NT ntName] tlSyms
                                    [stok] ptoks' (Fcons hdTree Fnil) tlTrees) in H.

                 

                            

                                           
                                        
           

(* I think we need to break gamma into two parts *)
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym tokens,
      (@derivesSym g) sym tokens tr
      -> (@derivesSym g) sym tokens tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym tokens,
                (@derivesSym g) sym tokens tr
                -> (@derivesSym g) sym tokens tr'
                -> tr = tr')
      (P0 := fun fSuf =>
               forall fSuf' fPre x gamma tokens,
                 In (x, gamma) (productions g)
                 -> (@derivesGamma g) gamma
                                      tokens
                                      (appF fPre fSuf)
                 -> (@derivesGamma g) gamma
                                      tokens
                                      (appF fPre fSuf')
                 -> fSuf = fSuf').

  - intros tr' sym tokens Hder Hder'.
    inv Hder.
    + inv Hder'.
      auto.
    + inv H.

  - intros tr' sym tokens Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    rename s into x.
    destruct Htbl as [Hmin Hcom].
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite IHtr; eauto.
      * rewrite <- appF_nil_l in H7.
        eauto.
      * rewrite <- appF_nil_l in H0.
        auto.
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite IHtr; eauto.
      * rewrite <- appF_nil_l in H7.
        eauto.
      * rewrite <- appF_nil_l in H0.
        auto.

  - intros fSuf' fPre x gamma tokens Hin Hder Hder'.
    rewrite appF_nil_r in Hder.
    destruct fSuf'.
    + auto.
    + exfalso.
      apply forest_length in Hder.
      apply forest_length in Hder'.
      rewrite Hder in Hder'.
      apply lengths_contra in Hder'.
      inv Hder'.

  - intros fSuf' fPre x gamma tokens Hin Hder Hder'.
    inv Hder; inv Hder'.
    + exfalso.
      eapply appF_Fcons_not_Fnil.
      eauto.
    + destruct hdSym as [tName | ntName].
      * inv H0.
        inv H6.
        inv H4.
        assert ((@derivesGamma g) (T tName :: tlSyms)
                                  (tName :: suffix)
                                  (Fcons (Leaf tName) tlTrees)).
        { eapply derivesFcons with (prefix := [tName]).
          { constructor. }
          { auto. }}
        assert ((@derivesGamma g) (T tName :: tlSyms)
                                  (tName :: suffix)
                                  (Fcons (Leaf tName) tlTrees0)).
        { eapply derivesFcons with (prefix := [tName]).
          { constructor. }
          { auto. }}
        rewrite H in H0.
        assert (Fcons (Leaf tName) tlTrees0 =
                appF (Fcons (Leaf tName) Fnil) tlTrees0).
        { simpl. auto. }
        rewrite H2 in H1.
        clear H2.
        eapply IHtr0 in H1.
        -- subst.
           inv H0.
           
        assert (appF fPre (Fcons tr f) =
                appF (appF fPre (Fcons tr Fnil)) f).
        { admit. }
        rewrite H0 in H.
        

      
          
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym tokens,
      (@derivesSym g) sym tokens tr
      -> (@derivesSym g) sym tokens tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' sym tokens,
                (@derivesSym g) sym tokens tr
                -> (@derivesSym g) sym tokens tr'
                -> tr = tr')
      (* maybe say something about what gammaPrefix derives *)
      (P0 := fun f =>
               forall f' x gammaPrefix gamma tokens,
                 In (x, gammaPrefix ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma tokens f
                 -> (@derivesGamma g) gamma tokens f'
                 -> f = f').

  - intros tr' sym tokens Hder Hder'.
    inv Hder; inv Hder'.
    + auto.
    + inv H.

  - intros tr' sym tokens Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    pose proof H7 as Hder.
    pose proof H0 as Hder'.
    rename s into x.
    destruct Htbl as [Hmin Hcom].
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite IHtr; eauto.
      assert (gamma0 = [] ++ gamma0) by auto.
      rewrite H1 in H.
      eauto.

    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      erewrite IHtr; eauto.
      assert (gamma0 = [] ++ gamma0) by auto.
      rewrite H1 in H.
      eauto.

  - intros f' x gammaPrefix gamma tokens Hin Hder Hder'.
    inv Hder; inv Hder'.
    auto.

  - intros f' x gammaPrefix gamma tokens Hin Hder Hder'.
    inv Hder; inv Hder'.
    destruct hdSym as [tName | ntName].
    + inv H2.
      inv H3.
      inv H1.
      eapply IHtr0 in H6; subst; eauto.
      assert (T tName :: tlSyms = [T tName] ++ tlSyms) by auto.
      rewrite H in Hin.
      rewrite app_assoc in Hin.
      eauto.
    + destruct Htbl as [Hmin Hcom].
      destruct prefix as [| ptok ptoks].
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- (* prefix is nil, prefix0 is nil *)
          subst.
          apply IHtr in H2; auto.
          eapply IHtr0 in H6; eauto.
          ++ subst.
             auto.
          ++ assert (NT ntName :: tlSyms =
                     [NT ntName] ++ tlSyms) by auto.
             rewrite H in Hin.
             rewrite app_assoc in Hin.
             eauto.
        -- (* prefix is nil, prefix0 is ptok' :: ptoks' *)
          destruct suffix as [| stok stoks].
          ++ inv H1.
          ++ 
Abort.

Lemma derivesProd_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gamma tokens,
      (@derivesProd g) x gamma tokens tr
      -> (@derivesProd g) x gamma tokens tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P := fun tr =>
              forall tr' x gamma tokens,
                (@derivesProd g) x gamma tokens tr
                -> (@derivesProd g) x gamma tokens tr'
                -> tr = tr')
      (P0 := fun f =>
               forall f' x gammaPrefix gamma tokens,
                 In (x, gammaPrefix ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma tokens f
                 -> (@derivesGamma g) gamma tokens f'
                 -> f = f').

  - intros tr' x gamma tokens Hder Hder'.
    inv Hder.

  - intros tr' x gamma tokens Hder Hder'.
    inv Hder.
    inv Hder'.
    erewrite IHtr; eauto.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    eauto.

  - intros f' x gammaPrefix gamma tokens Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    auto.

  - intros f' x gammaPrefix gamma tokens Hin Hder Hder'.
    inv Hder.
    inv Hder'.
    destruct hdSym as [tName | ntName].
    + inv H2.
      inv H3.
      inv H1.
      eapply IHtr0 in H6; subst; eauto.
      assert (T tName :: tlSyms = [T tName] ++ tlSyms) by auto.
      rewrite H in Hin.
      rewrite app_assoc in Hin.
      eauto.
    + destruct Htbl as [Hmin Hcom].
      inv H2.
      inv H3.
      inv H0.
      inv H2.
      destruct prefix as [| ptok ptoks].
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- (* prefix is nil, suffix is nil *)
          pose proof H3 as Hder.
          pose proof H5 as Hder'.
          apply derivesGamma_nil_nullable in H3.
          apply derivesGamma_nil_nullable in H5.
          assert (Hlk : (@isLookaheadFor g) EOF ntName gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              repeat (econstructor; eauto). }
          assert (Hlk' : (@isLookaheadFor g) EOF ntName gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              repeat (econstructor; eauto). }
          unfold ptComplete in Hcom.
          apply Hcom in Hlk.
          apply Hcom in Hlk'.
          destruct Hlk as [laMap [Hsf Hlf]].
          destruct Hlk' as [laMap' [Hsf' Hlf']].
          assert (gamma = gamma0) by congruence.
          subst.
          assert ((@derivesProd g) ntName
                                   gamma0
                                   []
                                   (Node ntName f0))
            by repeat (constructor; auto).
          assert ((@derivesProd g) ntName
                                   gamma0
                                   []
                                   (Node ntName f1))
            by repeat (constructor; auto).
          apply IHtr in H1; auto.
          inv H1.
          eapply IHtr0 in H6; eauto.
          ++ subst; auto.
          ++ assert (NT ntName :: tlSyms =
                     [NT ntName] ++ tlSyms) by auto.
             rewrite H1 in Hin.
             rewrite app_assoc in Hin.
             eauto.
        -- (* prefix is nil, prefix0 is cons *)
          destruct suffix as [| stok stoks].
          ++ inv H1.
          ++ (* [] ++ (stok :: stoks) = 
                (ptok' :: ptoks') ++ suf0

                stok :: stoks = ptok' :: ptoks' *)
            symmetry in H1.
            inv H1.
            assert (Hlk : (@isLookaheadFor g) (LA ptok')
                                              ntName
                                              gamma).
            { unfold isLookaheadFor.
              left.
              constructor; auto.
              apply derivesGamma_cons_firstGamma in H3.
              auto. }
            assert (Hlk' : (@isLookaheadFor g) (LA ptok')
                                               ntName
                                               gamma0).
            { unfold isLookaheadFor.
              right.
              split.
              { constructor; auto.
                apply derivesGamma_nil_nullable in H5.
                auto. }
              { constructor; auto.
                eapply FoRight; eauto.
                apply derivesGamma_cons_firstGamma in H4.
                auto. }}
            unfold ptComplete in Hcom.
            apply Hcom in Hlk; apply Hcom in Hlk'.
            destruct Hlk as [laMap [Hsf Hlf]].
            destruct Hlk' as [laMap' [Hsf' Hlf']].
            assert (gamma = gamma0) by congruence.
            subst.
            clear Hsf Hsf' Hlf Hlf' laMap laMap'.
            (* looking good -- we've reached a first/follow
               conflict, but I don't think that's quite 
               enough to finish. Maybe try switching the
               proof from derivesProd to derivesSym *)
            
            
      
 
Lemma derivesProd_det :
  forall tbl g x gamma tokens tr,
    isParseTableFor tbl g
    -> (@derivesProd g) x gamma tokens tr
    -> forall tr',
        (@derivesProd g) x gamma tokens tr'
        -> tr = tr'.
Proof.
  intros tbl g x gamma tokens tr Htbl Hder.
  induction Hder using derivesProd_mutual_ind with
      (P := fun x gamma tokens tr
                (pf : (@derivesProd g) x gamma tokens tr) =>
              forall tr',
                (@derivesProd g) x gamma tokens tr'
                -> tr = tr')
      (P0 := fun sym tokens tr
                 (pf : (@derivesSym g) sym tokens tr) =>
               forall tr',
                 (@derivesSym g) sym tokens tr'
                 -> tr = tr')
      (P1 := fun gamma tokens f
                 (pf : (@derivesGamma g) gamma tokens f) =>
               forall x gammaPrefix f',
                 In (x, gammaPrefix ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma tokens f'
                 -> f = f').

  - intros tr' Hder.
    inv Hder.
    apply (IHHder x nil f0) in H0; subst; auto.
    
  - intros tr' Hder.
    inv Hder.
    auto.

  - intros tr' Hder'.
    inv Hder.
    inv Hder'.
    inv H2.
    pose proof H0 as Hder.
    pose proof H3 as Hder'.
    destruct Htbl as [Hmin Hcom].
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      apply IHHder.
      constructor; auto.
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      apply IHHder.
      constructor; auto.

  - intros x gammaPrefix f' Hin Hder.
    inv Hder.
    auto.

  - intros x gammaPrefix f' Hin Hder.
    inv Hder.
    assert (Heq : gammaPrefix ++ hdSym :: tlSyms =
            gammaPrefix ++ [hdSym] ++ tlSyms) by auto.
    rewrite Heq in Hin.
    rewrite app_assoc in Hin.
    destruct hdSym as [tName | ntName].
    + inv d; inv H2.
      inv H1.
      apply IHHder0 with
          (x := x)
          (gammaPrefix := app gammaPrefix [T tName])
          (f' := tlTrees0) in Hin; auto.
      subst.
      auto.
    + destruct prefix as [| ptok ptoks];
        destruct prefix0 as [| ptok' ptoks']; simpl in *.

      * (* prefix and prefix0 are nil *)
        subst.
        apply IHHder in H2.
        subst.
        apply IHHder0 with
            (x := x)
            (gammaPrefix := app gammaPrefix [NT ntName])
            (f' := tlTrees0) in Hin; auto.
        subst; auto.
      * (* prefix is nil, prefix0 is cons *)
        (* we should be able to get a first/follow contra? *)
        destruct suffix as [| stok stoks];
          destruct suffix0 as [| stok' stoks']; simpl in *.
        -- inv H1.
        -- inv H1. 
        -- inv H1.
           rewrite app_nil_r in *.
           inv H2.
           inv H0.
           assert (Hlk : (@isLookaheadFor g) (LA stok) ntName gamma).
           { unfold isLookaheadFor.
             left.
             constructor; auto.
             apply derivesGamma_cons_firstGamma in H1.
             auto. }
           inv d.
           inv H2.
           assert (Hlk' : (@isLookaheadFor g) (LA stok) ntName gamma0).
           { unfold isLookaheadFor.
             right.
             split.
             { constructor; auto.
               apply derivesGamma_nil_nullable in H3; auto. }
             { constructor; auto.
               eapply FoRight.
               { (* hmm, Heq got corrupted somehow *)
                 assert ([NT ntName] ++ tlSyms =
                         NT ntName :: tlSyms) by auto.
                 rewrite <- app_assoc in Hin.
                 rewrite H2 in Hin.
                 eauto. }
               { apply derivesGamma_cons_firstGamma in d0.
                 auto. }}}
           destruct Htbl as [Hmin Hcom].
           unfold ptComplete in Hcom.
           apply Hcom in Hlk.
           apply Hcom in Hlk'.
           destruct Hlk as [laMap [Hsf Hlf]].
           destruct Hlk' as [laMap' [Hsf' Hlf']].
           assert (Hgammas : gamma = gamma0) by congruence.
           subst.
           clear Hsf; clear Hlf; clear Hsf'; clear Hlf'.
           clear laMap; clear laMap'.
Abort. (* seems promising, but I think the induction has
          to be more general *)

Lemma derivesProd_det :
  forall tbl g x gamma tokens tr,
    isParseTableFor tbl g
    -> (@derivesProd g) x gamma tokens tr
    -> forall tr',
        (@derivesProd g) x gamma tokens tr'
        -> tr = tr'.
Proof.
  intros tbl g x gamma tokens tr Htbl Hder.
  induction Hder using derivesProd_mutual_ind with
      (P := fun x gamma tokens tr
                (pf : (@derivesProd g) x gamma tokens tr) =>
              forall tr',
                (@derivesProd g) x gamma tokens tr'
                -> tr = tr')
      (P0 := fun sym tokens tr
                 (pf : (@derivesSym g) sym tokens tr) =>
               forall tr',
                 (@derivesSym g) sym tokens tr'
                 -> tr = tr')
      (P1 := fun gamma tokens f
                 (pf : (@derivesGamma g) gamma tokens f) =>
               forall f',
                 (@derivesGamma g) gamma tokens f'
                 -> f = f').
  
  - intros tr' Hder.
    inv Hder.
    apply IHHder in H0; auto.
    subst.
    auto.
    
  - intros tr' Hder.
    inv Hder.
    auto.

  - intros tr' Hder'.
    inv Hder.
    inv Hder'.
    inv H2.
    pose proof H0 as Hder.
    pose proof H3 as Hder'.
    destruct Htbl as [Hmin Hcom].
    destruct tokens as [| tok toks].
    + apply derivesGamma_nil_nullable in Hder.
      apply derivesGamma_nil_nullable in Hder'.
      assert (Hlk : (@isLookaheadFor g) EOF x gamma).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      assert (Hlk' : (@isLookaheadFor g) EOF x gamma0).
      { unfold isLookaheadFor.
        right.
        split.
        - constructor; auto.
        - constructor; auto.
          repeat (econstructor; eauto). }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      apply IHHder.
      constructor; auto.
    + apply derivesGamma_cons_firstGamma in Hder.
      apply derivesGamma_cons_firstGamma in Hder'.
      assert (Hlk : (@isLookaheadFor g) (LA tok) x gamma).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      assert (Hlk' : (@isLookaheadFor g) (LA tok) x gamma0).
      { unfold isLookaheadFor.
        left.
        constructor; auto. }
      unfold ptComplete in Hcom.
      apply Hcom in Hlk.
      apply Hcom in Hlk'.
      destruct Hlk as [laMap [Hsf Hlf]].
      destruct Hlk' as [laMap' [Hsf' Hlf']].
      assert (gamma = gamma0) by congruence.
      subst.
      apply IHHder.
      constructor; auto.

  - intros f' Hder.
    inv Hder.
    auto.

  - intros f' Hder. 
    inv Hder.
Abort.
(* The problem here is that we don't know that (hdSym :: tlSyms) is the RHS of some production in the grammar, so we probably
  won't be able to prove that prefix = prefix0, hdTree = tr',
  etc. *)