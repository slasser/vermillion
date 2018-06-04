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

Lemma tree_eq_dec : forall (tr tr2 : tree),
    {tr = tr2} + {~tr = tr2}.
Proof.
Admitted.

Lemma forest_eq_dec : forall (f f2 : forest),
    {f = f2} + {~f = f2}.
Proof.
Admitted.

Lemma prefixes_eq :
  forall (suf pre pre' : list string),
    app pre suf = app pre' suf
    -> pre = pre'.
Proof.
  induction suf; intros; simpl in *.
  - repeat rewrite app_nil_r in H.
    auto.
  - assert (a :: suf = app [a] suf) by auto.
    repeat rewrite H0 in H.
    repeat rewrite app_assoc in H.
    apply IHsuf in H.
    apply app_inj_tail in H.
    destruct H.
    auto.
Qed.

Lemma suffixes_eq :
  forall (pre suf suf' : list string),
    app pre suf = app pre suf'
    -> suf = suf'.
Proof.
  induction pre; intros; simpl in *.
  - auto.
  - inv H.
    apply IHpre; auto.
Qed.

Fixpoint inF tr f :=
  match f with
  | Fnil => False
  | Fcons tr' f' =>
    tr = tr' \/ inF tr f'
  end.

Lemma forest_neq :
  forall f f' tr tr',
    Fcons tr f <> Fcons tr' f'
    -> tr <> tr' \/ f <> f'.
Proof.
  intros.
  destruct (forest_eq_dec f f').
  - subst.
    left.
    unfold not; intros.
    subst.
    congruence.
  - right; auto.
Qed.

Lemma eof_fgamma :
  forall g la gamma,
    (@firstGamma g) la gamma
    -> la = EOF
    -> False.
Proof.
  intros g la gamma H.
  induction H using firstGamma_mutual_ind with
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

Lemma derives_lookahead :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym word,
      (@derivesSym g) sym word tr
      -> (@firstSym g) (peek word) sym
         \/ ((@nullableSym g) sym
             /\ (@followSym g) (peek word) sym).
Proof.
  intros.
  inv H0.
  - left.
    simpl.
    constructor.
  - destruct word.
    + inv H1.
      right.
      simpl.
      apply derivesGamma_nil_nullable in H2.
      split.
      * econstructor.
        econstructor; eauto.
      * eapply FoNu; eauto.
        econstructor; eauto.
    + inv H1.
      left.
      simpl.
      apply derivesGamma_cons_firstGamma in H2.
      econstructor.
      econstructor; eauto.
Qed.

Lemma derivesGamma_lookahead :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma f word,
      (@derivesGamma g) gamma word f
      -> (@firstGamma g) (peek word) gamma
         \/ (@nullableGamma g) gamma.
Proof.
  intros tbl g Htbl.
  induction gamma; intros; simpl in *.
  - inv H.
    right; constructor.
  - inv H.
    destruct prefix; simpl in *.
    + apply IHgamma in H5.
      destruct H5.
      * destruct suffix; simpl in *.
        -- apply eof_fgamma in H.
           ++ inv H.
           ++ auto.
        -- left.
           destruct a.
           ++ inv H2.
           ++ eapply FiGammaTl.
              ** inv H2.
                 inv H1.
                 apply derivesGamma_nil_nullable in H2.
                 econstructor.
                 econstructor; eauto.
              ** auto.
      * right.
        destruct a.
        -- inv H2.
        -- eapply NuCons.
           ++ inv H2.
              inv H1.
              apply derivesGamma_nil_nullable in H2.
              econstructor.
              econstructor; eauto.
           ++ auto.
    + destruct a.
      * inv H2.
        left.
        constructor.
        constructor.
      * inv H2.
        inv H0.
        apply derivesGamma_cons_firstGamma in H1.
        left.
        constructor.
        econstructor.
        econstructor; eauto.
Qed.

Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym word tr,
      (@derivesTree g) sym word tr
      -> forall tr',
        (@derivesTree g) sym word tr'
        -> tr = tr'.
Proof.
  intros tbl g Htbl sym word tr Hder.
  induction Hder using derivesTree_mutual_ind with
      (P := fun sym word tr =>
              forall tr',
                (@derivesTree g) sym word tr'
                -> tr = tr')
      (P0 := fun gsuf wsuf fsuf =>
                 derivesForest gsuf wsuf fsuf
                 -> forall x gpre wpre wpre' wsuf wsuf' fpre fpre' fsuf',
                     In (x, gpre ++ gsuf) (productions g)
                     -> derivesForest gpre wpre fpre
                     -> derivesForest gpre wpre' fpre'
                     -> derivesForest gsuf wsuf' fsuf'
                     -> wpre ++ wsuf = wpre' ++ wsuf'
                     -> wpre = wpre'
                        /\ wsuf = wsuf'
                        /\ fsuf = fsuf').

  - intros.
    inv H.
    auto.

  - intros.
    inv H1.
    assert (gamma0 = gamma) by admit; subst.
    eapply IHHder with (gpre := nil)
                       (wpre := nil)
                       (fpre := Fnil) in H4; eauto.
    + destruct H4.
      destruct H2.
      subst; auto.
    + constructor.
    + constructor.

  - intros.
    inv H.
    inv H3.
    repeat rewrite app_nil_r in *.
    subst.
    assert (wsuf = nil) by admit.
    subst.
    repeat (split; auto).
    rewrite app_nil_r.
    auto.
    
  - intros.
    inv H1.
    


Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr'
              x
              gpre wpre wpre' fpre fpre'
              sym  wmid wmid'
              gsuf wsuf wsuf' fsuf fsuf',
      In (x, gpre ++ sym :: gsuf) (productions g)
         
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesGamma g) gpre wpre' fpre'
                           
      -> (@derivesSym g) sym wmid tr
      -> (@derivesSym g) sym wmid' tr'
                           
      -> (@derivesGamma g) gsuf wsuf fsuf
      -> (@derivesGamma g) gsuf wsuf' fsuf'
                           
      -> wpre ++ wmid = wpre' ++ wmid'
      -> wmid ++ wsuf = wmid' ++ wsuf'
                              
      -> wpre = wpre'
         /\ wmid = wmid'
         /\ wsuf = wsuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun fmid =>
               forall fmid'
                      x
                      gpre wpre wpre' fpre fpre'
                      gmid wmid wmid'
                      gsuf wsuf wsuf' fsuf fsuf',
      In (x, gpre ++ gmid ++ gsuf) (productions g)
         
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesGamma g) gpre wpre' fpre'
                           
      -> (@derivesGamma g) gmid wmid fmid
      -> (@derivesGamma g) gmid wmid' fmid'
                           
      -> (@derivesGamma g) gsuf wsuf fsuf
      -> (@derivesGamma g) gsuf wsuf' fsuf'
                           
      -> wpre ++ wmid = wpre' ++ wmid'
      -> wmid ++ wsuf = wmid' ++ wsuf'
                              
      -> wpre = wpre'
         /\ wmid = wmid'
         /\ wsuf = wsuf'
         /\ fmid = fmid').
  - intros.
    inv H2.
    + inv H3.
      inv H7.
      apply prefixes_eq in H6.
      subst.
      repeat (split; auto).
    + inv H8.
      
  - intros.
    inv H2; inv H3.
    inv H8; inv H9.
    assert (gamma0 = gamma) by admit; subst.
Abort.

Fixpoint forest_det f g :=
  match f with
  | Fnil => forall gamma word f',
      (@derivesGamma g) gamma word f
      -> (@derivesGamma g) gamma word f'
      -> f = f'
  | Fcons tr tl =>
    (forall sym word tr',
        (@derivesSym g) sym word tr
        -> (@derivesSym g) sym word tr'
        -> tr = tr')
    /\ forest_det tl g
  end.

Lemma ambig :
  forall g sym word tr,
    (@derivesSym g) sym word tr
    -> forall tr',
      (@derivesSym g) sym word tr'
      -> tr <> tr'
      -> exists x gamma gamma' word' f f',
          In (x, gamma) (productions g)
          /\ In (x, gamma') (productions g)
          /\ (@derivesGamma g) gamma word' f
          /\ (@derivesGamma g) gamma' word' f'
          /\ gamma <> gamma'.
Proof.
  intros g sym word tr Hder.
  induction Hder using derivesSym_mut_ind
    with (P := fun x gamma word tr
                   (pf : (@derivesProd g) x gamma word tr) =>
                 forall tr',
                   (@derivesProd g) x gamma word tr'
                   -> tr <> tr'
                   -> exists x gamma gamma' word' f f',
                       In (x, gamma) (productions g)
                       /\ In (x, gamma') (productions g)
                       /\ (@derivesGamma g) gamma word' f
                       /\ (@derivesGamma g) gamma' word' f'
                       /\ gamma <> gamma')
         (P0 := fun gsuf wsuf fsuf
                   (pf : (@derivesGamma g) gsuf wsuf fsuf) =>
                  forall x gpre wpre fpre fsuf',
                    In (x, gpre ++ gsuf) (productions g)
                    -> (@derivesGamma g) gpre wpre fpre
                    -> (@derivesGamma g) gsuf wsuf fsuf'
                    -> fsuf <> fsuf'
                   -> exists x gamma gamma' word' f f',
                       In (x, gamma) (productions g)
                       /\ In (x, gamma') (productions g)
                       /\ (@derivesGamma g) gamma word' f
                       /\ (@derivesGamma g) gamma' word' f'
                       /\ gamma <> gamma').
  - intros.
    inv H.
    eapply IHHder with (gpre := nil)
      in H2; eauto.
    + constructor.
    + destruct (forest_eq_dec f f0).
      * subst.
        congruence.
      * auto.

  - intros.
    inv H1.
    congruence.

  - intros.
    inv H1.












    
    
Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  
  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    erewrite IHtr; eauto.

  - intros.
    inv H.
    inv H0.
    auto.

  - intros.
    inv H; inv H0.
Abort.




Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym wpre wpre' wsuf wsuf',
      (@derivesSym g) sym wsuf tr
      -> (@derivesSym g) sym wsuf' tr'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> wpre = wpre'
         /\ wsuf = wsuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall fsuf'
                      gpre wpre wpre' fpre fpre'
                      gsuf wsuf wsuf',
                 (@derivesGamma g) gpre wpre fpre
                 -> (@derivesGamma g) gpre wpre' fpre'
                 -> (@derivesGamma g) gsuf wsuf fsuf
                 -> (@derivesGamma g) gsuf wsuf' fsuf'
                 ->  wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf').
  - admit.
  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with (gpre := nil)
                     (wpre := nil)
                     (wpre' := nil) in H0; eauto.
Abort.    



(* trying just prefixes *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x
              gpre wpre wpre' fpre fpre'
              sym  wmid wmid'
              gsuf,
              (* gsuf wsuf wsuf' fsuf fsuf', *)
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesGamma g) gpre wpre' fpre'
      -> (@derivesSym g) sym wmid tr
      -> (@derivesSym g) sym wmid' tr'
(*
      -> (@derivesGamma g) gsuf wsuf fsuf
      -> (@derivesGamma g) gsuf wsuf' fsuf'
*)
      -> wpre ++ wmid = wpre' ++ wmid'
      -> wpre = wpre'
         /\ wmid = wmid'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall 
                      gpre wpre wpre' fpre fpre'
                      gsuf wsuf wsuf'      fsuf',
                 (@derivesGamma g) gpre wpre fpre
                 -> (@derivesGamma g) gpre wpre' fpre'
                 -> (@derivesGamma g) gsuf wsuf fsuf
                 -> (@derivesGamma g) gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fsuf = fsuf').
  - intros.
    inv H2.
    + inv H3.
      apply prefixes_eq in H4.
      subst.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H2; inv H3.
    inv H5; inv H6.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with
        (gpre := gpre)
        (wpre := wpre)
        (wpre' := wpre')
        (gsuf := gamma)
        (wsuf := wmid)
        (wsuf' := wmid') in H3; eauto.
    destruct H3.
    destruct H5.
    subst.
    repeat (split; auto).

  - intros.
    inv H1; inv H2.
    repeat rewrite app_nil_r in *; subst.
    repeat (split; auto).

  - intros.
    inv H1; inv H2.
    pose proof H10 as H10'.
    eapply IHtr0 with
        (gpre := gpre ++ [hdSym])
        (wpre := wpre ++ prefix)
        (wpre' := wpre' ++ prefix0) in H10; eauto.
    + destruct H10.
      destruct H2.
      subst.
      eapply IHtr with
          (gpre := gpre)
          (wpre := wpre)
          (wpre' := wpre')
          (wmid := prefix)
          (wmid' := prefix0) in H5; eauto.
      * destruct H5.
        destruct H4.
        subst.
        repeat (split; auto).
      * admit.
    + eapply derives_app.
      * eauto.
      * admit.
    + admit.
    + repeat rewrite <- app_assoc.
      auto.
Abort. (* pretty close! *)


(* three-part word *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x
              gpre wpre wpre' fpre fpre'
              sym  wmid wmid'
              gsuf wsuf wsuf' fsuf fsuf',
      
      In (x, gpre ++ sym :: gsuf) (productions g)
         
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesGamma g) gpre wpre' fpre'
                           
      -> (@derivesSym g) sym wmid tr
      -> (@derivesSym g) sym wmid' tr'

      -> (@derivesGamma g) gsuf wsuf fsuf
      -> (@derivesGamma g) gsuf wsuf' fsuf'

      -> wmid ++ wsuf = wmid' ++ wsuf'
      -> wpre ++ wmid ++ wsuf = wpre' ++ wmid' ++ wsuf'

      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall x
                      gpre wpre wpre' fpre fpre'
                      gsuf wsuf wsuf'      fsuf',
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gpre wpre fpre
                 -> (@derivesGamma g) gpre wpre' fpre'
                 -> (@derivesGamma g) gsuf wsuf fsuf
                 -> (@derivesGamma g) gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> fsuf = fsuf').
  - intros.
    inv H2.
    + inv H3.
      auto.
    + inv H8.

  - intros.
    inv H2; inv H3.
    inv H8; inv H9.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with
        (gpre := nil)
        (wpre := nil)
        (wpre' := nil)
        (gsuf := gamma)
        (wsuf := wmid)
        (wsuf' := wmid') in H3; eauto.
Abort. (* IH doesn't have the right form *)

Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym word tr,
      (@derivesSym g) sym word tr
      -> forall tr',
        (@derivesSym g) sym word tr'
        -> tr = tr'.
Proof.
  intros tbl g Htbl sym word tr Hder.
  induction Hder using derivesSym_mut_ind with
      (P := fun x gamma word tr
                (pf : (@derivesProd g) x gamma word tr) =>
              forall tr',
                (@derivesProd g) x gamma word tr'
                -> tr = tr')
      (P0 := fun gsuf wsuf fsuf
                 (pf : (@derivesGamma g) gsuf wsuf fsuf) =>
               forall x gpre wpre fpre,
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gpre wpre fpre
                 -> forall wpre' fpre' wsuf' fsuf',
                     (@derivesGamma g) gpre wpre' fpre'
                     -> (@derivesGamma g) gsuf wsuf' fsuf'
                     -> wpre ++ wsuf = wpre' ++ wsuf'
                     -> wpre = wpre'
                        /\ wsuf = wsuf'
                        /\ fsuf = fsuf').
  - intros.
    inv H.
    eapply IHHder with
        (gpre := nil)
        (wpre := nil) in H1; eauto.
    + destruct H1.
      destruct H1.
      subst; auto.
    + constructor.
    + constructor.
      
  - intros.
    inv H2.
    repeat rewrite app_nil_r in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H2.
    eapply IHHder0 with 
        (gpre := gpre ++ [hdSym])
        (wpre := wpre ++ prefix)
        (wpre' := wpre' ++ prefix0)
        (fpre := appF fpre (Fcons hdTree Fnil))
        (fpre' := appF fpre' (Fcons hdTree0 Fnil))
        (wsuf' := suffix0) in H9; eauto.
    * destruct H9.
      destruct H4.
      subst.
      (* can't apply IHHder here *)
      admit.
      * assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
        rewrite H2 in H.
        rewrite app_assoc in H.
        eauto.
      * apply derives_app with
            (gPre := gpre)
            (wPre := wpre)
            (fPre := fpre)
            (gSuf := [hdSym])
            (wSuf := prefix)
            (fSuf := Fcons hdTree Fnil).
        -- auto.
        -- assert (prefix = prefix ++ nil) by
              (rewrite app_nil_r; auto).
           rewrite H2.
           eapply derivesFcons; eauto.
           constructor.
      * apply derives_app with
            (gPre := gpre)
            (wPre := wpre')
            (fPre := fpre')
            (gSuf := [hdSym])
            (wSuf := prefix0)
            (fSuf := Fcons hdTree0 Fnil).
        -- auto.
        -- assert (prefix0 = prefix0 ++ nil) by
              (rewrite app_nil_r; auto).
           rewrite H2.
           eapply derivesFcons; eauto.
           constructor.
      * repeat rewrite <- app_assoc.
        auto.
        
  - intros.
    inv H.
    auto.

  - intros.
    inv d.

    inv H.
    inv H3.
    assert (gamma0 = gamma) by admit.
    subst.
    apply IHHder.
    constructor; auto.
Abort. (* So close! *)


(* Most promising so far? *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym wmid tr,
      (@derivesSym g) sym wmid tr
      -> forall x
                gpre wpre fpre
                gsuf wsuf fsuf,
        In (x, gpre ++ sym :: gsuf) (productions g)
        -> (@derivesGamma g) gpre wpre fpre
        -> (@derivesGamma g) gsuf wsuf fsuf
        -> forall wpre' fpre'
                  wmid' tr'
                  wsuf' fsuf',
            (@derivesSym g) sym wmid' tr'
            -> (@derivesGamma g) gpre wpre' fpre'
            -> (@derivesGamma g) gsuf wsuf' fsuf'
            -> wpre ++ wmid ++ wsuf = wpre' ++ wmid' ++ wsuf'
            -> wmid = wmid'
               /\ tr = tr'.
Proof.
  intros tbl g Htbl sym wmid tr Hder.
  induction Hder using derivesSym_mut_ind with
      (P := fun x gamma word tr
                (pf : (@derivesProd g) x gamma word tr) =>
              forall tr',
                (@derivesProd g) x gamma word tr'
                -> tr = tr')
      (P0 := fun gsuf wsuf fsuf
                 (pf : (@derivesGamma g) gsuf wsuf fsuf) =>
               forall x gpre wpre fpre,
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gpre wpre fpre
                 -> forall wpre' fpre' wsuf' fsuf',
                     (@derivesGamma g) gpre wpre' fpre'
                     -> (@derivesGamma g) gsuf wsuf' fsuf'
                     -> wpre ++ wsuf = wpre' ++ wsuf'
                     -> wpre = wpre'
                        /\ wsuf = wsuf'
                        /\ fsuf = fsuf').
  - intros.
    inv H.
    eapply IHHder with
        (gpre := nil)
        (wpre := nil) in H1; eauto.
    + destruct H1.
      destruct H1.
      subst; auto.
    + constructor.
    + constructor.
      
  - intros.
    inv H2.
    repeat rewrite app_nil_r in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H2.
    eapply IHHder0 with
        (gpre := gpre ++ [hdSym])
        (wpre := wpre ++ prefix)
        (wpre' := wpre' ++ prefix0) in H9; eauto.
    + destruct H9.
      destruct H4.
      subst.
      eapply IHHder with
          (wpre := wpre)
          (wpre' := wpre')
          (wmid' := prefix0)
          (wsuf := suffix0)
          (wsuf' := suffix0) in H6; eauto.
      destruct H6.
      subst.
      apply prefixes_eq in H2.
      repeat (split; auto).
    + admit.
    + admit.
    + admit.
    + repeat rewrite <- app_assoc.
      auto.

  - intros.
    inv H2.
    split; auto.

  - intros.
    inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
Abort.
(* Looking even better, though! *)

(* trying to remove the different suffixes -- that works *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym wmid tr,
      (@derivesSym g) sym wmid tr
      -> forall x
                gpre wpre fpre
                gsuf wsuf fsuf,
        In (x, gpre ++ sym :: gsuf) (productions g)
        -> (@derivesGamma g) gpre wpre fpre
        -> (@derivesGamma g) gsuf wsuf fsuf
        -> forall wpre' fpre'
                  wmid' tr',
            (@derivesSym g) sym wmid' tr'
            -> (@derivesGamma g) gpre wpre' fpre'
            -> wpre ++ wmid = wpre' ++ wmid'
            -> wpre = wpre'
               /\wmid = wmid'
               /\ tr = tr'.
Proof.
  intros tbl g Htbl sym wmid tr Hder.
  induction Hder using derivesSym_mut_ind with
      (P := fun rx gamma wmid tr
                (pf : (@derivesProd g) rx gamma wmid tr) =>
              forall lx gpre wpre fpre
                        gsuf wsuf fsuf,
                In (lx, gpre ++ (NT rx) :: gsuf)
                   (productions g)
                -> (@derivesGamma g) gpre wpre fpre
                -> (@derivesGamma g) gsuf wsuf fsuf
                -> forall wpre' fpre' wmid' tr',
                    (@derivesGamma g) gpre wpre' fpre'
                    -> (@derivesProd g) rx gamma wmid' tr'
                    -> wpre ++ wmid = wpre' ++ wmid'
                    -> wpre = wpre'
                       /\ wmid = wmid'
                       /\ tr = tr')
      (P0 := fun gsuf wsuf fsuf
                 (pf : (@derivesGamma g) gsuf wsuf fsuf) =>
               forall x gpre wpre fpre,
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gpre wpre fpre
                 -> forall wpre' fpre' wsuf' fsuf',
                     (@derivesGamma g) gpre wpre' fpre'
                     -> (@derivesGamma g) gsuf wsuf' fsuf'
                     -> wpre ++ wsuf = wpre' ++ wsuf'
                     -> wpre = wpre'
                        /\ wsuf = wsuf'
                        /\ fsuf = fsuf').
  - intros.
Abort. (* IH problems *)

  

Lemma derives_det :
    forall tbl g,
    isParseTableFor tbl g
    -> forall sym wpre tr syms wsuf f,
        (@derivesSym g) sym wpre tr
        -> (@derivesGamma g) syms wsuf f
        -> forall wpre' tr' wsuf' f',
            (@derivesSym g) sym wpre' tr'
            -> (@derivesGamma g) syms wsuf' f'
            -> wpre ++ wsuf = wpre' ++ wsuf'
            -> wpre = wpre'
               /\ wsuf = wsuf'
               /\ tr = tr.
Proof.
  intros tbl g Htbl sym wpre tr syms wsuf f Hders.
  induction Hders using derivesSym_mut_ind with
      (P := fun 
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesSym g) sym wmid tr
      -> (@derivesGamma g) gsuf wsuf fsuf

      -> forall wpre' fpre' wmid' tr' wsuf' fsuf',
          wpre ++ wmid ++ wsuf = wpre' ++ wmid' ++ wsuf'
          -> (@derivesGamma g) gpre wpre' fpre'
          -> (@derivesSym g) sym wmid' tr'
          -> (@derivesGamma g) gsuf wsuf' fsuf'
                         
          -> tr = tr'.

(* three-part word *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
                    
    -> forall x
              gpre wpre fpre
              sym  wmid tr
              gsuf wsuf fsuf,
      In (x, gpre ++ sym :: gsuf) (productions g)
      -> (@derivesGamma g) gpre wpre fpre
      -> (@derivesSym g) sym wmid tr
      -> (@derivesGamma g) gsuf wsuf fsuf

      -> forall wpre' fpre' wmid' tr' wsuf' fsuf',
          wpre ++ wmid ++ wsuf = wpre' ++ wmid' ++ wsuf'
          -> (@derivesGamma g) gpre wpre' fpre'
          -> (@derivesSym g) sym wmid' tr'
          -> (@derivesGamma g) gsuf wsuf' fsuf'
                         
          -> tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun fsuf =>
               forall x
                      gpre wpre wpre' fpre fpre'
                      gsuf wsuf wsuf'      fsuf',
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gpre wpre fpre
                 -> (@derivesGamma g) gpre wpre' fpre'
                 -> (@derivesGamma g) gsuf wsuf fsuf
                 -> (@derivesGamma g) gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> fsuf = fsuf').






    
(* Input is empty, symbol could be T or NT *)
Lemma derives_nil_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym,
      (@derivesSym g) sym [] tr
      -> (@derivesSym g) sym [] tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma,
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma [] f
                 -> (@derivesGamma g) gamma [] f'
                 -> f = f').
  - intros.
    inv H.
    inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    inv H1.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0.
    inv H1.
    auto.

  - intros.
    inv H0.
    inv H1.
    assert (prefix = []) by admit.
    assert (prefix0 = []) by admit.
    assert (suffix = []) by admit.
    assert (suffix0 = []) by admit.
    subst.
    assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
    rewrite H0 in H.
    rewrite app_assoc in H.
    erewrite IHtr; eauto.
    erewrite IHtr0; eauto.
Admitted.

Lemma derives_cons_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym tok toks,
      (@derivesSym g) sym (tok :: toks) tr
      -> (@derivesSym g) sym (tok :: toks) tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gpre gsuf tok toks,
                 In (x, gpre ++ gsuf) (productions g)
                 -> (@derivesGamma g) gsuf (tok :: toks) f
                 -> (@derivesGamma g) gsuf (tok :: toks) f'
                 -> f = f').
  - intros.
    inv H.
    + inv H0.
      auto.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    erewrite IHtr with (gpre := nil); eauto.

  - intros.
    inv H0.

  - intros.
    inv H0.
    inv H1.
    destruct prefix; simpl in *.
    + destruct prefix0; simpl in *.
      * subst.
        eapply IHtr0 with (gpre := gpre ++ [hdSym])
          in H9; eauto.
        -- subst.
           eapply derives_nil_det in H6; eauto.
        subst; auto.
        -- admit.
      * inv H4.
        admit.
    + destruct prefix0; simpl in *.
      * inv H2.
        admit.
      * inv H2.
        inv H4.
        

Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym wpre wpre' wsuf wsuf',
      (@derivesSym g) sym wpre tr
      -> (@derivesSym g) sym wpre' tr'
      -> wpre ++ wsuf = wpre' ++ wsuf'
      -> peek (wpre ++ wsuf) = peek (wpre' ++ wsuf')
      -> wpre = wpre'
         /\ wsuf = wsuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma wpre wpre' wsuf wsuf',
                 (@derivesGamma g) gamma wpre f
                 -> (@derivesGamma g) gamma wpre' f'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> peek (wpre ++ wsuf) = peek (wpre' ++ wsuf')
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ f = f').
  - intros.
    inv H.
    + inv H0.
      inv H1.
      repeat (split; auto).
    + inv H3.
      
  - intros.
    inv H; inv H0.
    inv H3; inv H4.
    assert (gamma0 = gamma).
    { pose proof H9 as H9'.
      apply derivesGamma_lookahead with (tbl := tbl) in H9; auto.
      pose proof H0 as H0'.
      apply derivesGamma_lookahead with (tbl := tbl) in H0; auto.
      destruct wpre; simpl in *.
      - destruct H9.
        + apply eof_fgamma in H3; auto.
          inv H3.
        + destruct wpre'; simpl in *.
          * destruct H0.
            -- apply eof_fgamma in H0; auto.
               inv H0.
            -- admit.
          * admit.
      - destruct wpre'.

Abort.









    

Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  - admit.
  - admit.
  - admit.
  - intros.
    inv H; inv H0.
    eapply derives_lookahead in H5.
    

Lemma derives_with_res_and_stuff :
    forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr'
              x gPre sym gSuf
              wPre wPre' wSuf wSuf'
              f f' res res',
        In (x, gPre ++ sym :: gSuf) (productions g)
        -> (@derivesSym g) sym wPre tr
        -> (@derivesSym g) sym wPre' tr'
        -> (@derivesGamma g) gSuf wSuf f
        -> (@derivesGamma g) gSuf wSuf' f'
        -> wPre ++ wSuf ++ res = wPre' ++ wSuf' ++ res'
        -> (wPre = wPre'
            /\ (wSuf ++ res) = (wSuf' ++ res')
            /\ tr = tr').
Proof.
  intros tbl g Htbl.
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gSuf wPre wPre' wSuf wSuf',
                 In (x, gPre ++ gSuf) (productions g)
                 -> (@derivesGamma g) gSuf wPre f
                 -> (@derivesGamma g) gSuf wPre' f'
                 -> wPre ++ wSuf = wPre' ++ wSuf'
                 -> wPre = wPre'
                    /\ wSuf = wSuf'
                    /\ f = f').
  - intros.
    inv H0.
    + inv H1.
      inv H4.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with (gPre := nil) in H1; eauto.
    destruct H1.
    destruct H5.
    subst.
    repeat (split; auto).

  - intros.
    inv H0; inv H1.
    simpl in *; subst.
    repeat (split; auto).

  - intros.
    inv H0; inv H1.
    eapply IHtr with
        (wSuf := suffix)
        (wSuf' := suffix0)
        (res := wSuf)
        (res' := wSuf') in H4; eauto.
    + destruct H4.
      destruct H1.
      subst.
      eapply IHtr0 in H9; eauto.
      * destruct H9.
        destruct H3.
        subst.
        repeat (split; auto).
      * assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
        rewrite H0 in H.
        rewrite app_assoc in H.
        eauto.
    + repeat rewrite <- app_assoc in H2.
      auto.
Abort.


Lemma derives_det :
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
      (P0 := fun fpre =>
               forall x fpre' gpre gsuf wpre wpre' wsuf wsuf' fsuf fsuf',
                 (@derivesGamma g) gpre wpre fpre
                 -> (@derivesGamma g) gpre wpre' fpre'
                 -> (@derivesGamma g) gsuf wsuf fsuf
                 -> (@derivesGamma g) gsuf wsuf' fsuf'
                 -> wpre ++ wsuf = wpre' ++ wsuf'
                 -> wpre = wpre'
                    /\ wsuf = wsuf'
                    /\ fpre = fpre').
  - intros.
    inv H.
    + inv H0; auto.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit; subst.
    eapply IHtr with (gpre := gamma)
                     (gsuf := nil) in H0; eauto.
    + destruct H0.
      destruct H1.
      subst; auto.
    + constructor.
    + constructor.

  - intros.
    inv H.
    inv H0.
    simpl in *; subst.
    repeat (split; auto).

  - intros.
    inv H.
    inv H0.
Abort.


(* Here's what we really want to prove *)
Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  
  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    erewrite IHtr; eauto.

  - intros.
    inv H.
    inv H0.
    auto.

  - intros.
    inv H; inv H0.
    + (* here, we're going to get stuck because we don't know
         whether prefix = prefix0. It would help if we knew
         that prefix and prefix0 shared the first lookahead
         token *)
Abort.

Fixpoint lenF f :=
  match f with
  | Fnil => 0
  | Fcons tr f' => 1 + lenF f'
  end.

(* trying the length idea *)
Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> lenF f = lenF f'
                    /\ f = f').
  - admit.
  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr in H0; eauto.
    destruct H0.
    subst; auto.
  - intros.
    inv H.
    inv H0.
    split; auto.
  - intros.
    inv H.
    inv H0.
    simpl.



Lemma derives_det :
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
      (P0 := fun fSuf =>
               forall gPre wPre wPre' fPre fPre'
                      gSuf wSuf wSuf'      fSuf',
                 (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gPre wPre' fPre'
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf wSuf' fSuf'
                 -> wPre ++ wSuf = wPre' ++ wSuf'
                 -> wPre = wPre'
                    /\ wSuf = wSuf'
                    /\ fSuf = fSuf').
  - intros.
    inv H.
    + inv H0.
      auto.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with
        (gPre := nil)
        (wPre := nil)
        (wPre' := nil)
        (fPre := Fnil)
        (fPre' := Fnil) in H0; eauto.
    + destruct H0.
      destruct H1.
      simpl in H2.
      subst.
      auto.
    + constructor.
    + constructor.

  - intros.
    inv H1.
    inv H2.
    repeat rewrite app_nil_r in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H1.
    inv H2.
    eapply IHtr0 with
        (gPre := gPre ++ [hdSym])
        (wPre := wPre ++ prefix)
        (wPre' := wPre' ++ prefix0)
        (wSuf := suffix) in H10; eauto.
    + destruct H10.
      destruct H2.
      subst.
Abort.

(* Here's what we really want to prove *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gPre sym gSuf wPre wPre' wSuf wSuf' f f',
      In (x, gPre ++ sym :: gSuf) (productions g)
      -> (@derivesSym g) sym wPre tr
      -> (@derivesSym g) sym wPre' tr'
      -> (@derivesGamma g) gSuf wSuf f
      -> (@derivesGamma g) gSuf wSuf' f'
      -> wPre ++ wSuf = wPre' ++ wSuf'
      -> wPre = wPre'
         /\ wSuf = wSuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fSuf =>
               forall gPre gSuf
                      wPre wPre' wSuf wSuf'
                      fPre fPre'      fSuf',
                 (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gPre wPre' fPre'
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf wSuf' fSuf'
                 -> wPre ++ wSuf = wPre' ++ wSuf'
                 -> wPre = wPre'
                    /\ wSuf = wSuf'
                    /\ fSuf = fSuf').
  - intros.
    inv H0.
    + inv H1.
      inv H4.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    assert (gamma0 = gamma) by admit.
    subst.
Abort.
  


Lemma only_one_span :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> span tr = span tr'.
Proof.
  intros tbl g.
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> spanForest f = spanForest f').
  - intros.
    inv H0.
    + inv H1.
      auto.
    + inv H2.

  - intros.
    inv H0; inv H1.
    inv H2; inv H3.
    simpl.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr; eauto.

  - intros.
    inv H0; inv H1.
    auto.

  - intros.
    simpl.
    inv H0; inv H1.
    simpl.
Abort.



Lemma only_one_split :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gPre gSuf
              wPre wPre' wSuf wSuf'
              fPre fPre' fSuf fSuf',
      (@derivesGamma g) gPre wPre fPre
      -> (@derivesGamma g) gPre wPre' fPre'
      -> (@derivesGamma g) gSuf wSuf fSuf
      -> (@derivesGamma g) gSuf wSuf' fSuf'
      -> wPre ++ wSuf = wPre' ++ wSuf'
      -> appF fPre fSuf = appF fPre' fSuf'
      -> wPre = wPre'
         /\ wSuf = wSuf'.
Proof.
  intros tbl g Htbl.
  induction gPre as [| psym psyms]; intros.
  - inv H; inv H0.
    simpl in *; subst.
    split; auto.
  - inv H; inv H0.
    simpl in H4.
    inv H4.
    assert (prefix0 = prefix) by admit.
    subst.
    repeat rewrite <- app_assoc in H3.
    apply suffixes_eq in H3.
    eapply IHpsyms with (gSuf := gSuf)
                        (wPre := suffix)
                        (wPre' := suffix0)
                        (wSuf := wSuf)
                        (wSuf' := wSuf') in H11; eauto.
    destruct H11.
    subst.
    split; auto.
Admitted.


Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').
  - intros.
    inv H.
    + inv H0.
      auto.
    + inv H1.

  - intros.
    inv H.
    inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    erewrite IHtr; eauto.

  - intros.
    inv H.
    inv H0.
    auto.

  - intros.
    inv H.
    inv H0.
Abort.
  

(* Problem : in the last case, we can't prove that 
   gamma and gamma0 are equal *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall sym wPre tr,
      (@derivesSym g) sym wPre tr
      -> forall wPre' wSuf wSuf' tr',
        (@derivesSym g) sym wPre' tr'
        -> wPre ++ wSuf = wPre' ++ wSuf'
        -> wPre = wPre'
           /\ wSuf = wSuf'
           /\ tr = tr'.
Proof.
  intros tbl g Htbl sym word tr Hder.
  induction Hder using derivesSym_mut_ind with
      (P := fun x gamma wPre tr
                (pf : (@derivesProd g) x gamma wPre tr) =>
              forall wPre' wSuf wSuf' tr',
                (@derivesProd g) x gamma wPre' tr'
                -> wPre ++ wSuf = wPre' ++ wSuf'
                -> wPre = wPre'
                   /\ wSuf = wSuf'
                   /\ tr = tr')
      (P0 := fun gamma wPre f
                 (pf : (@derivesGamma g) gamma wPre f) =>
                  forall wPre' wSuf wSuf' f',
                    (@derivesGamma g) gamma wPre' f'
                    -> wPre ++ wSuf = wPre' ++ wSuf'
                    -> wPre = wPre'
                       /\ wSuf = wSuf'
                       /\ f = f').
  - intros.
    inv H.
    eapply IHHder in H2; eauto.
    destruct H2.
    destruct H2.
    subst.
    repeat (split; auto).

  - intros.
    inv H.
    simpl in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H.
    eapply IHHder with
        (wSuf := suffix ++ wSuf)
        (wSuf' := suffix0 ++ wSuf') in H3; eauto.
    + destruct H3.
      destruct H1.
      subst.
      eapply IHHder0 in H6; eauto.
      destruct H6.
      destruct H2.
      subst.
      repeat (split; auto).
    + repeat rewrite app_assoc.
      auto.
      
  - intros.
    inv H.
    inv H0.
    repeat (split; auto).

  - intros.
    inv H.
    assert (gamma0 = gamma) by admit.
    subst.
Abort.
















  

Lemma derives_det :
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
      (P0 := fun fSuf =>
               forall x gPre gSuf,
                 In (x, gPre ++ gSuf) (productions g)
                 -> (forall wPre wPre'
                            wSuf wSuf'
                            fPre fPre',
                        (@derivesGamma g) gPre wPre fPre
                        -> (@derivesGamma g) gPre wPre' fPre'
                        -> wPre ++ wSuf = wPre' ++ wSuf'
                        -> wPre = wPre'
                           /\ wSuf = wSuf'
                           /\ fPre = fPre')
                 -> forall wPre fPre
                           wPre' fPre'
                           wSuf wSuf'
                           fSuf',
                     (@derivesGamma g) gPre wPre fPre
                     -> (@derivesGamma g) gPre wPre' fPre'
                     -> (@derivesGamma g) gSuf wSuf fSuf
                     -> (@derivesGamma g) gSuf wSuf' fSuf'
                     -> wPre ++ wSuf = wPre' ++ wSuf'
                     -> wPre = wPre'
                        /\ wSuf = wSuf'
                        /\ fSuf = fSuf').

  - intros.
    inv H.
    + inv H0.
      auto.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with (gPre := nil)
                     (wPre := nil)
                     (wPre' := nil) in H0; eauto.
    + destruct H0.
      destruct H1.
      subst.
      auto.
    + intros.
      inv H1; inv H2.
      simpl in *; subst.
      repeat (split; auto).
    + constructor.
    + constructor.

  - intros.
    inv H3.
    inv H4.
    repeat rewrite app_nil_r in *; subst.
    repeat (split; auto).

  - intros.
    inv H3; inv H4.
    eapply H0 with (wPre := wPre)
                   (wPre' := wPre') in H2; eauto.
    destruct H2.
    destruct H3.
    subst.
    eapply IHtr0 with
        (gPre := gPre ++ [hdSym])
        (gSuf := tlSyms) in H12; eauto.
    + destruct H12.
      destruct H4.
      subst.
      eapply IHtr in H7; eauto.
      subst.
      repeat (split; auto).
    + assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
      rewrite H2 in H.
      rewrite app_assoc in H.
      eauto.
    + admit.
    + admit.
    + admit.
Abort.
    


(* SOME THINGS TO TRY TODAY
   ========================
   - What do tr and tr' tell us about word and word' ?

   - Can we show that if words are equal and trees are not equal,
     then there are two (x, gamma)'s that derive the same word?

   - Go back to earlier attempts, but add the fact that gPre accepts
     some wPre *)     



Lemma ambig_exists :
  forall g tr tr' sym word,
    (@derivesSym g) sym word tr
    -> (@derivesSym g) sym word tr'
    -> tr <> tr'
    -> exists x2 gamma1 gamma2 word' f f',
        In (x2, gamma1) (productions g)
        /\ In (x2, gamma2) (productions g)
        /\ (@derivesGamma g) gamma1 word' f
        /\ (@derivesGamma g) gamma2 word' f'
        /\ gamma1 <> gamma2.
Proof.
  intro g.
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f'
                      x gPre wPre fPre
                      gSuf gSuf' wSuf,
                 In (x, gPre ++ gSuf) (productions g)
                 -> In (x, gPre ++ gSuf') (productions g)
                 -> (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gSuf wSuf f
                 -> (@derivesGamma g) gSuf' wSuf f'
                 -> f <> f'
                 -> exists x gamma1 gamma2 word' f1 f2,
                     In (x, gamma1) (productions g)
                     /\ In (x, gamma2) (productions g)
                     /\ (@derivesGamma g) gamma1 word' f1
                     /\ (@derivesGamma g) gamma2 word' f2
                     /\ gamma1 <> gamma2).

  - intros.
    admit.
    

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    destruct (list_eq_dec symbol_eq_dec gamma gamma0).
    + subst.
      eapply IHtr with (gPre := nil)
                       (wPre := nil)
                       (fPre := Fnil) in H0; eauto.
      * constructor.
      * unfold not; intros; congruence.
    + exists s; exists gamma; exists gamma0.
      repeat eexists; eauto.

  - intros.
    inv H2; inv H3.
    + congruence.
    + exists x.
      exists gPre.
      exists (gPre ++ hdSym :: tlSyms).
      exists wPre.
      exists fPre.
      exists (appF fPre (Fcons hdTree tlTrees)).
      repeat (split; auto).
      * admit.
      * admit.
      * admit.

  - intros.
    inv H2.
    inv H3.
    + admit.
    + 

  - intros.
    inv H; inv H0.
 


    
      * admit.
        (*destruct H2.
        repeat destruct H0.
        destruct H2.
        destruct H3.
        destruct H4.
        exists x.
        exists (x0 ++ x1).
        exists (x0 ++ x2).
        repeat eexists; repeat (split; eauto). auto. auto.
        repeat eexists; eauto. *)
      * unfold not; intros.
        subst.
        congruence.
    + exists s. exists gamma; exists gamma'; exists word;
                  exists f; exists f0.
      repeat (split; auto).

  - intros.
    exists x; exists gPre; exists gSuf; exists gSuf';
      exists word; exists Fnil; exists f'.
    repeat (split; auto).
    destruct (list_eq_dec symbol_eq_dec gSuf gSuf').
    + subst.
      inv H1.
      inv H2.
      congruence.
    + auto.

  - intros.
    
                                          


                    fSuf =>
               forall x
                      gPre wPre fPre
                      gSuf wSuf 
                      gSuf' wSuf' fSuf',
                 In (x, gPre ++ gSuf) (productions g)
                 -> In (x, gPre ++ gSuf') (productions g)
                 -> (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf' wSuf' fSuf'
                 -> (fSuf = fSuf' -> gSuf = gSuf'
                                     /\ wSuf = wSuf')
                    /\ (fSuf <> fSuf' -> gSuf <> gSuf'
                                   \/ wSuf <> wSuf')).
  induction word as [| tok toks]; intros.
  - inv H.
    inv H0.
    destruct 
  


  
Lemma what_syms_and_trees_tells_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym'
                      /\ word = word')
         /\ (tr <> tr' -> sym <> sym'
                          \/ word <> word').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fSuf =>
               forall x
                      gPre wPre fPre
                      gSuf wSuf 
                      gSuf' wSuf' fSuf',
                 In (x, gPre ++ gSuf) (productions g)
                 -> In (x, gPre ++ gSuf') (productions g)
                 -> (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf' wSuf' fSuf'
                 -> (fSuf = fSuf' -> gSuf = gSuf'
                                     /\ wSuf = wSuf')
                    /\ (fSuf <> fSuf' -> gSuf <> gSuf'
                                   \/ wSuf <> wSuf')).

  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H.
           split; auto.
        -- left.
           unfold not; intros.
           congruence.
      * inv H.
        split; intros.
        -- congruence.
        -- left; congruence.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros.
      * congruence.
      * left; congruence.
    + inv H.
      split; intros.
      * inv H.
        eapply IHtr with (gPre := nil)
                         (wPre := nil)
                         (fPre := Fnil)
                         (gSuf := gamma) in H1; eauto.
        -- destruct H1.
           destruct H; auto.
        -- constructor.
      * destruct (string_dec s x).
        -- subst.
           destruct (list_eq_dec string_dec word word').
           ++ subst.
              assert (gamma0 = gamma) by admit.
              subst.
              eapply IHtr with (gPre := nil)
                               (wPre := nil)
                               (fPre := Fnil)
                               (gSuf := gamma) in H1; eauto.
              ** destruct H1.
                 destruct (forest_eq_dec f f0).
                 --- congruence.
                 --- apply H2 in n.
                     destruct n; congruence.
              ** constructor.
           ++ right; congruence.
        -- left; congruence.

  - intros.
    inv H2.
    inv H3.
    + split; intros.
      * split; auto.
      * congruence.
    + split; intros.
      * congruence.
      * left; congruence.

  - intros.
    inv H2.
    inv H3.
    + split; intros.
      * congruence.
      * left; congruence.
    + split; intros.
      * inv H3.
        eapply IHtr with (sym := hdSym)
                         (word := prefix) in H2; eauto.
        destruct H2.
        destruct H2; subst; auto.
        eapply IHtr0 with (gPre := gPre ++ [hdSym0])
                          (wPre := wPre ++ prefix0)
                          (fPre := appF fPre
                                        (Fcons hdTree Fnil))
                          (wSuf := suffix) in H4; eauto.
        
        -- destruct H4.
           destruct H2; auto; subst.
           split; auto.
        -- assert (hdSym0 :: tlSyms =
                   [hdSym0] ++ tlSyms) by auto.
           rewrite H2 in H.
           rewrite app_assoc in H.
           eauto.
        -- assert (hdSym0 :: tlSyms0 = [hdSym0] ++ tlSyms0)
            by auto.
           rewrite H2 in H0.
           rewrite app_assoc in H0.
           auto.
        -- eapply derives_app; eauto.
           assert (prefix0 = prefix0 ++ nil)
                  by (rewrite app_nil_r; auto).
           rewrite H2.
           eapply derivesFcons with (hdSym := hdSym0)
                                    (prefix := prefix0)
                                    (suffix1 := nil)
                                    (hdTree0 := hdTree)
                                    (tlSyms1 := nil)
                                    (tlTrees0 := Fnil).
           ++ auto.
           ++ constructor.
      * Abort.


Lemma what_syms_and_trees_tells_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym'
                      /\ word = word')
         /\ (tr <> tr' -> sym <> sym'
                          \/ word <> word').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma gamma' word word',
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (f = f' -> gamma = gamma'
                               /\ word = word')
                    /\ (f <> f' -> gamma <> gamma'
                                   \/ word <> word')).

  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H.
           split; auto.
        -- left.
           unfold not; intros.
           congruence.
      * inv H.
        split; intros.
        -- congruence.
        -- left; congruence.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros.
      * congruence.
      * left; congruence.
    + inv H.
      pose proof H1 as H1'.
      eapply IHtr in H1; eauto.
      destruct H1.
      split; intros.
      * inv H2.
        destruct H; auto.
      * destruct (string_dec s x).
        -- subst.
           destruct (list_eq_dec string_dec word word').
           ++ subst.
              assert (gamma0 = gamma) by admit.
              subst.
              destruct (forest_eq_dec f f0).
              ** congruence.
              ** apply H1 in n.
                 destruct n; congruence.
           ++ auto.
        -- left; congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros.
      * split; auto.
      * congruence.
    + split; intros.
      * congruence.
      * left; congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros.
      * congruence.
      * left; congruence.
    + split; intros.
      * inv H0.
        eapply IHtr with (word := prefix) in H; eauto.
        destruct H.
        eapply IHtr0 with (word := suffix) in H1; eauto.
        destruct H1.
        destruct H; auto.
        subst.
        destruct H1; auto.
        subst.
        split; auto.
      * destruct (list_eq_dec string_dec (prefix ++ suffix)
                              (prefix0 ++ suffix0)).
        -- pose proof H as H'.
           eapply IHtr with (word := prefix) in H; eauto.
           destruct H.
           pose proof H1 as H1'.
           eapply IHtr0 with (word := suffix) in H1; eauto.
           destruct H1.
           destruct (tree_eq_dec tr hdTree).
           ++ subst.
              assert (hdSym = hdSym0 /\ prefix = prefix0)
                by auto.
              destruct H4; subst.
              apply suffixes_eq in e; subst.
              destruct (forest_eq_dec f tlTrees).
              ** subst; congruence.
              ** apply H3 in n.
                 destruct n.
                 --- left; congruence.
                 --- congruence.
           ++ apply H2 in n.
              ** destruct n.
                 --- left; congruence.
                 --- admit. (* stuck! *)
        -- right; auto.
Admitted.










(* Maybe try this with just the "positive" part? *)
Lemma what_sym_and_words_tells_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gamma gamma' word word',
      (@derivesProd g) x gamma word tr
      -> (@derivesProd g) x gamma' word' tr'
      -> (word = word'
          -> gamma = gamma
             /\ tr = tr')
         /\ (word <> word'
             -> gamma <> gamma'
                /\ tr <> tr').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fSuf =>
               forall fSuf' x gPre gSuf gSuf'
                      wPre wSuf wSuf' fPre,
                 In (x, gPre ++ gSuf) (productions g)
                 -> In (x, gPre ++ gSuf') (productions g)
                 -> (@derivesGamma g) gPre wPre fPre 
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf' wSuf' fSuf'
                 -> (wSuf = wSuf'
                     -> gSuf = gSuf'
                        /\ fSuf = fSuf')
                    /\ (wSuf <> wSuf'
                        -> gSuf <> gSuf'
                           /\ fSuf <> fSuf')).

  - intros.
    inv H.

  - intros.
    inv H.
    inv H0.
    split; intros.
    + subst.
      assert (gamma' = gamma) by admit.
      subst.
      assert (gamma = [] ++ gamma) by auto.
      rewrite H0 in H.
      eapply IHtr in H1; eauto.
      * destruct H1.
        destruct H1; auto.
        subst.
        split; auto.
      * econstructor.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H2 in H6.
      assert (gamma' = [] ++ gamma') by auto.
      rewrite H3 in H.
      eapply IHtr with (gPre := nil)
                       (gSuf := gamma)
                       (wSuf := word) in H1; eauto.
      * destruct H1.
        apply H4 in H0.
        destruct H0.
        split; congruence.
      * constructor.

  - intros.
    inv H2.
    inv H3.
    + split; intros.
      * split; auto.
      * congruence.
    + split; intros.
      * exfalso.
        assert (prefix = nil) by admit.
        assert (suffix = nil) by admit.
        subst.
        destruct wPre as [| tok toks].
        -- assert ((@derivesGamma g) (gPre ++ hdSym :: tlSyms)
                                     []
                                     (appF fPre
                                           (Fcons hdTree tlTrees))).
           { admit. }
           assert ((@derivesGamma g) gPre
                                     []
                                     (appF fPre
                                           (Fcons hdTree tlTrees))).
           { admit. }
           apply derivesGamma_nil_nullable in H5.
           apply derivesGamma_nil_nullable in H6.
           assert ((@isLookaheadFor g) EOF (NT x) gPre).
           { admit. }
           assert ((@isLookaheadFor g) EOF (NT x)
                                       (gPre ++ hdSym :: tlSyms)).
           { admit. }
           apply Hcom in H7.
           apply Hcom in H8.
           destruct H7 as [m [Hsf Hlf]].
           destruct H8 as [m' [Hsf' Hlf']].
           assert (gPre =
                   (gPre ++ hdSym :: tlSyms)) by congruence.
           admit.

        -- admit.
      * split; congruence.

  - intros.
    inv H2.
    inv H3.
    + split; intros.
      * admit.
      * split; congruence.
    + split; intros.
      * 










      



  

Lemma what_sym_and_words_tells_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (sym = sym'
          -> word = word'
          -> tr = tr')
         /\ (sym <> sym'
             -> word <> word'
             -> tr <> tr').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma gamma' word word',
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (gamma = gamma'
                     -> word = word'
                     -> f = f')
                    /\ (gamma <> gamma'
                        -> word <> word'
                        -> f <> f')).

  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H; auto.
        -- unfold not; intros.
           inv H1.
           congruence.
      * inv H.
        split; intros; congruence.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros; congruence.
    + inv H.
      split; intros.
      * inv H.
        assert (gamma0 = gamma) by admit.
        subst.
        eapply IHtr in H1; eauto.
        destruct H1.
        destruct H; auto.
      * unfold not; intros.
        inv H3.
        congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros; congruence.
    + split; intros; congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros; congruence.
    + split; intros.
      * inv H0.
        eapply IHtr with (word := prefix) in H; eauto.
        destruct H as [Hsymeq Hsymneq].
        eapply IHtr0 with (word := suffix) in H1; eauto.
        destruct H1 as [Htleq Htlneq].
        destruct (list_eq_dec string_dec prefix prefix0).
        -- subst.
           apply suffixes_eq in H2.
           subst.
           destruct Hsymeq; destruct Htleq; auto.
        -- destruct (list_eq_dec string_dec suffix suffix0).
           ++ subst.
              apply prefixes_eq in H2.
              subst.
              destruct Hsymeq; destruct Htleq; auto.
           ++ 
Abort.








    



Lemma what_sym_andor_words_tells_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (sym = sym'
          -> word = word'
          -> tr = tr')
         /\ ((sym <> sym'
              \/ word <> word')
             -> tr <> tr').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma gamma' word word',
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (gamma = gamma'
                     -> word = word'
                     -> f = f')
                    /\ ((gamma <> gamma'
                         \/ word <> word')
                        -> f <> f')).
  
  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H; auto.
        -- unfold not; intros.
           inv H0.
           destruct H; congruence.
      * inv H.
        split; intros; congruence.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros; congruence.
    + inv H.
      split; intros.
      * inv H.
        assert (gamma0 = gamma) by admit.
        subst.
        eapply IHtr with (word := word') in H1; eauto.
        destruct H1.
        destruct H; auto.
      * unfold not; intros.
        inv H2.
        destruct H.
        -- congruence.
        -- eapply IHtr with (word := word) in H1; eauto.
           destruct H1.
           assert (f0 <> f0) by auto.
           congruence.
           
  - intros.
    inv H.
    inv H0.
    + split; intros.
      * auto.
      * destruct H; congruence.
    + split; intros; congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros; congruence.
    + split; intros.
      * inv H0.
        eapply IHtr with (word := prefix) in H; eauto.
        destruct H as [Hsymeq Hsymneq].
        eapply IHtr0 with (word := suffix) in H1; eauto.
        destruct H1 as [Htleq Htlneq].
        destruct (list_eq_dec string_dec prefix prefix0).
        -- subst.
           apply suffixes_eq in H2.
           subst.
           destruct Hsymeq; destruct Htleq; auto.
        -- destruct (list_eq_dec string_dec suffix suffix0).
           ++ subst.
              apply prefixes_eq in H2.
              congruence.
           ++ admit.
      * Abort.

                       

    










  

Lemma what_trees_tell_us :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym' /\ word = word')
         /\ (tr <> tr' -> sym <> sym'
                          \/ word <> word').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma gamma' word word',
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (f = f'
                     -> gamma = gamma' /\ word = word')
                    /\ (f <> f' 
                        -> gamma <> gamma' \/ word <> word')).
  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H.
           split; auto.
        -- left.
           unfold not; intros.
           congruence.
      * inv H.
        split; intros.
        -- congruence.
        -- left; congruence.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros.
      * congruence.
      * left; congruence.
    + inv H.
      split; intros.
      * inv H.
        eapply IHtr with (word := word) in H1; eauto.
        destruct H1.
        destruct H; auto.
      * pose proof H1 as H1'.
        eapply IHtr with (word := word) in H1; eauto.
        destruct H1.
        destruct (string_dec s x).
        -- subst.
           destruct (forest_eq_dec f f0).
           ++ subst.
              destruct H1; auto.
           ++ apply H2 in n.
              ** destruct (list_eq_dec string_dec word word').
                 --- subst.
                     (* get this from LL(1)? *)
                     admit.
                 --- auto.
        -- left.
           congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros; auto.
    + split; intros.
      * congruence.
      * left; congruence.

  - intros.
    inv H.
    inv H0.
    + split; intros.
      * congruence.
      * left; congruence.
    + split; intros.
      * inv H0.
        eapply IHtr with (word := prefix) in H; eauto.
        destruct H.
        destruct H; auto.
        subst.
        eapply IHtr0 with (word := suffix) in H1; eauto.
        destruct H1.
        destruct H; auto.
        subst.
        split; auto.
      * eapply IHtr with (sym := hdSym)
                         (word := prefix) in H; eauto.
        destruct H as [Htreq Htrneq].
        eapply IHtr0 with (gamma := tlSyms)
                          (word := suffix) in H1; eauto.
        destruct H1 as [Hfeq Hfneq].
        destruct H. destruct (tree_eq_dec tr hdTree); subst.
        eapply IHtr with (word := prefix) in H; eauto.
        destruct H.
        -- destruct (forest_eq_dec f tlTrees); subst.
           ++ congruence.
           ++ (* heads eq, tails neq *)
             eapply IHtr with (word := prefix) in H; eauto.
             destruct H.
             destruct H; auto.
             subst.
             eapply IHtr0 with (word := suffix) in H1; eauto.
             destruct H1.
             apply H1 in n.
             destruct n.
             ** left; congruence.
             ** right.
                unfold not; intros.
                apply suffixes_eq in H4.
                congruence.
        -- destruct (forest_eq_dec f tlTrees); subst.
           ++ apply IHtr0 in 
             congruence.
        -- destruct (forest_eq_dec f tlTrees); subst.
           ++ (* heads neq, tails eq *)
             eapply IHtr with (word := prefix) in H; eauto.
             destruct H.
             apply H2 in n; auto.
             eapply IHtr0 with (word := suffix) in H1; eauto.
             destruct H1.
             destruct H1; auto.
             subst.
             congruence.

          pose proof H as H'.
           eapply IHtr with (word := prefix) in H; eauto.
           destruct H.
           apply H2 in n.
           destruct n.
           ++ congruence.
           ++ eapply IHtr0 with (word := suffix) in H1; eauto.
              destruct H1.
              destruct (forest_eq_dec f tlTrees).
              ** subst.
                 destruct H1; auto.
                 subst.
                 

             
             
             eapply IHtr with (word := prefix) in H; eauto.
             destruct H.
             destruct H; auto.
             subst.
             eapply IHtr0 with (word := suffix) in H1; eauto.
             destruct H1.
             apply H1 in n.
             destruct n.
             ** left.
                congruence.
             **  
               


        apply forest_neq in H0.
        destruct H0.
        -- pose proof H as H'.
           eapply IHtr with (word := prefix) in H; eauto.
           destruct H.
           apply H2 in H0.
           destruct H0.
           ++ left; congruence.
           ++ pose proof H1 as H1'.
              eapply IHtr0 with (word := suffix) in H1; eauto.
              destruct H1.
              destruct (forest_eq_dec f tlTrees).
              ** subst.
                 destruct H1; auto.
                 subst.






    
        
Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
      -> (word = word' -> tr = tr')
         /\ (word <> word' -> tr <> tr').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gSuf word word',
                 In (x, gPre ++ gSuf) (productions g)
                 -> (@derivesGamma g) gSuf word f
                 -> (@derivesGamma g) gSuf word' f'
                 -> (word = word' -> f = f')
                    /\ (word <> word' -> f <> f')).

  - intros.
    inv H.
    + inv H0.
      split; intros; auto.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    split; intros.
    + subst.
      assert (gamma0 = gamma) by admit.
      subst.
      assert (gamma = [] ++ gamma) by auto.
      rewrite H1 in H.
      eapply IHtr in H0; eauto.
      destruct H0.
      rewrite H0; auto.
    + unfold not; intros.
      inv H2. (* on the right track, but we don't know that
                 gamma and gamma0 are equal *)
Abort.


Lemma if_trees_eq_then_syms_and_words_eq :
  forall g tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym' /\ word = word')
         /\ (tr <> tr' -> sym <> sym'
                          \/ word <> word'
                          \/ exists x gamma1 gamma2
                                    word3
                                    f1 f2,
                              In (x, gamma1) (productions g)
                              /\ In (x, gamma2) (productions g)
                              /\ (@derivesGamma g) gamma1 word3 f1
                              /\ (@derivesGamma g) gamma2 word3 f2
                              /\ gamma1 <> gamma2).
Proof.
  intro g.
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma gamma' word word',
                 In (x, pre ++ gamma) (productions g)
                 -> In (x, pre ++ gamma') (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 ->  (f = f' -> gamma = gamma' /\ word = word')
                     /\ (f <> f' -> gamma <> gamma'
                                    \/ word <> word'
                                    \/ exists x2 gamma1 gamma2
                                              word3
                                              f1 f2,
                                        In (x2, gamma1) (productions g)
                                        /\ In (x2, gamma2) (productions g)
                                        /\ (@derivesGamma g) gamma1 word3 f1
                                        /\ (@derivesGamma g) gamma2 word3 f2
                                        /\ gamma1 <> gamma2)).
                                        

  - intros.
    inv H; inv H0.
    + split; intros.
      * inv H.
        split; auto.
      * left; unfold not; intros; congruence.
    + inv H.
      split; intros.
      * congruence.
      * left; unfold not; intros; congruence.
    + inv H1.
    + inv H1.

  - intros.
    inv H; inv H0.
    + inv H1.
      split; intros.
      * congruence.
      * left; congruence.
    + inv H1; inv H.
      split; intros.
      * inv H.
        eapply IHtr with
            (pre := nil)
            (gamma := gamma)
            (gamma' := gamma0) in H0; eauto.
        destruct H0.
        destruct H; auto.
      * 

    + auto.
  - intros.
    inv H1; inv H2.
    split; auto.
    
  - intros.
    inv H1; inv H2.
    eapply IHtr with
        (sym := hdSym) (word := prefix) in H6; auto.
    destruct H6; subst.
    eapply IHtr0 with
        (gamma := tlSyms) (word := suffix) in H9; auto.
    + destruct H9.
      subst; split; auto.
    + assert (hdSym0 :: tlSyms = [hdSym0] ++ tlSyms) by auto.
      rewrite H1 in H.
      rewrite app_assoc in H.
      eauto.
    + assert (hdSym0 :: tlSyms0 = [hdSym0] ++ tlSyms0) by auto.
      rewrite H1 in H0.
      rewrite app_assoc in H0.
      auto.
Qed.      

Lemma ambig_exists :
  forall tr tr' g sym word,
    (@derivesSym g) sym word tr
    -> (@derivesSym g) sym word tr'
    -> tr <> tr'
    -> exists x gamma gamma' word' f f',
        In (x, gamma) (productions g)
        /\ In (x, gamma') (productions g)
        /\ (@derivesGamma g) gamma word' f
        /\ (@derivesGamma g) gamma' word' f'
        /\ gamma <> gamma'.
Proof.
  induction tr using tree_mutual_ind with
      (P0 := fun fSuf =>
               forall fSuf' g x gPre gSuf gSuf' word,
                 In (x, gPre ++ gSuf) (productions g)
                 -> In (x, gPre ++ gSuf') (productions g)
                 -> (@derivesGamma g) gSuf word fSuf
                 -> (@derivesGamma g) gSuf' word fSuf'
                 -> fSuf <> fSuf'
                 -> gSuf <> gSuf'
                    \/ (exists x2 gamma gamma' word' f f',
                           In (x2, gamma) (productions g)
                           /\ In (x2, gamma') (productions g)
                           /\ (@derivesGamma g) gamma word' f
                           /\ (@derivesGamma g) gamma' word' f'
                           /\ gamma <> gamma')).
  
  - intros.
    inv H; inv H0.
    + congruence.
    + inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    pose proof H0 as H0'.
    eapply IHtr with (gPre := nil)
                     (gSuf := gamma)
                     (gSuf' := gamma0) in H0; eauto.
    + destruct H0.
      * exists s; exists gamma; exists gamma0.
        repeat eexists; eauto.
      * eauto.
    + unfold not; intros; congruence.

  - intros.
    inv H1; inv H2.
    + congruence.
    + left; congruence.

  - intros.
    inv H1; inv H2.
    + left; congruence.
    + 

    
    
      






      
    

Lemma ambig_exists :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma word x tr tr',
    (@derivesProd g) x gamma word tr
    -> (@derivesProd g) x gamma word tr'
    -> tr <> tr'
    -> exists x2 gamma' gamma'' w1 w2 w3 st st',
        In (NT x2) gamma
        /\ In (x2, gamma') (productions g)
        /\ In (x2, gamma'') (productions g)
        /\ word = w1 ++ w2 ++ w3
        /\ (@derivesProd g) x2 gamma' w2 st
        /\ (@derivesProd g) x2 gamma'' w2 st'
        /\ gamma' <> gamma'.
Proof.
  intros tbl g Htbl.
  induction gamma as [| sym syms].
  - intros.
    inv H.
    inv H0.
    admit.
  - intros.
    inv H; inv H0.
    inv H3; inv H4.
    inv H6; inv H7.
    + inv H5.
    
  inv H0; inv H1.

Ab

Lemma lemma4 :
  forall tbl g,
    isParseTableFor tbl g
    -> forall x x2 pre suf w1 w2 w3 gamma gamma' tr tr' f1 f3,
      In (x, pre ++ (NT x2) :: suf) (productions g)
      -> (@derivesGamma g) pre w1 f1
      -> (@derivesProd g) x2 gamma w2 tr
      -> (@derivesProd g) x2 gamma' w2 tr'
      -> (@derivesGamma g) suf w3 f3
      -> gamma = gamma' /\ tr = tr'.
Proof.
  intros.
  inv H2; inv H3.
  
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr'
              x pre sym suf
              wPre wPre'
              word word'
              wSuf wSuf'
              f f',
      In (x, pre ++ sym :: suf) (productions g)
      -> (@derivesSym g) sym wPre tr
      -> (@derivesSym g) sym wPre' tr'
      -> (@derivesGamma g) suf word f
      -> (@derivesGamma g) suf word' f'
      -> wPre ++ word = wPre' ++ word'
      -> word ++ wSuf = word' ++ wSuf'
      -> wPre = wPre'
         /\ word = word'
         /\ wSuf = wSuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma wPre wPre' wSuf wSuf',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma wPre f
                 -> (@derivesGamma g) gamma wPre' f'
                 -> wPre ++ wSuf = wPre' ++ wSuf'
                 -> wPre = wPre' /\ wSuf = wSuf' /\ f = f').
  
  - intros.
    inv H0; inv H1; auto.
    + inv H4.
      apply suffixes_eq in H5.
      subst.
      repeat (split; auto).
    + inv H6.

  - intros.
    inv H0; inv H1.
    inv H6; inv H7.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    eapply IHtr in H1; eauto.
    + destruct H1.
      destruct H6.
      subst.
      apply suffixes_eq in H5.
      subst.
      repeat (split; auto).
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H6 in H0.
      eauto.

  - intros.
    inv H0; inv H1.
    simpl in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H0.
    inv H1.
    eapply IHtr with
        (wPre := prefix)
        (wPre' := prefix0)
        (word := suffix)
        (word' := suffix0)
        (wSuf := wSuf)
        (wSuf' := wSuf') in H4; eauto.
    + destruct H4.
      destruct H1.
      destruct H9.
      destruct H3.
      subst.
      inv H8.
      * repeat (split; auto).
      * 
    + destruct H
    eapply IHtr0 with
        (wPre := wPre ++ prefix)
        (wPre' := wPre' ++ prefix0) in H9; eauto.
    + destruct H9.
      destruct H1.
      subst.
      eapply IHtr in H4; eauto.
      * destruct H4.
        destruct H3.
        destruct H4.
        subst.
        repeat (split; auto).
      * 
      
    destruct hdSym as [y | x2].
    + inv H6; inv H4.
      inv H3.
      assert (T y :: tlSyms = [T y] ++ tlSyms) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      erewrite IHtr0; eauto.
    + (* here, we're going to get stuck because we don't know
         whether prefix = prefix0. It would help if we knew
         that prefix and prefix0 shared the first lookahead
         token *)
Abort.


(* Here's what we really want to prove *)
Lemma derives_det :
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
      (P0 := fun f =>
               forall f' x pre gamma word,
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  
  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0; inv H1.
    auto.

  - intros.
    inv H0.
    inv H1.
    destruct hdSym as [y | x2].
    + inv H6; inv H4.
      inv H3.
      assert (T y :: tlSyms = [T y] ++ tlSyms) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      erewrite IHtr0; eauto.
    + (* here, we're going to get stuck because we don't know
         whether prefix = prefix0. It would help if we knew
         that prefix and prefix0 shared the first lookahead
         token *)
Abort.

Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x
              pre sym suf
              word word'
              wSuf wSuf'
              f f',
      In (x, pre ++ sym :: suf) (productions g)
      -> (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
      -> (@derivesGamma g) suf wSuf f
      -> (@derivesGamma g) suf wSuf' f'
      -> word ++ wSuf = word' ++ wSuf'
      -> word = word'
         /\ wSuf = wSuf'
         /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma wPre wPre' wSuf wSuf',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma wSuf f
                 -> (@derivesGamma g) gamma wSuf' f'
                 -> wPre ++ wSuf = wPre' ++ wSuf'
                 ->  wPre = wPre'
                     /\ wSuf = wSuf'
                     /\ f = f').
  - intros.
    inv H0; inv H1; auto.
    + inv H4.
      subst.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    assert (gamma0 = gamma) by admit; subst.
    eapply IHtr in H1; eauto.
    + destruct H1.
      destruct H5.
      subst.
      apply suffixes_eq in H4.
      subst.
      repeat (split; auto).
    + admit.
    + 
      
  - intros.
    inv H0; inv H1.
    repeat rewrite app_nil_r in *.
    subst.
    repeat (split; auto).

  - intros.
    inv H0; inv H1.
    pose proof H9 as H9'.
    eapply IHtr0 with
        (wPre := wPre ++ prefix)
        (wPre' := wPre' ++ prefix0) in H9; eauto.
    + destruct H9.
      destruct H1.
      subst.
      eapply IHtr in H4; eauto.
      * destruct H4.
        destruct H3.
        destruct H4.
        subst.
        repeat (split; auto).
      * 

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x
              gPre
              sym word word' 
              gSuf wSuf wSuf' fSuf fSuf',
      
      In (x, gPre ++ sym :: gSuf) (productions g)
                           
      -> (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
                         
      -> (@derivesGamma g) gSuf wSuf fSuf
      -> (@derivesGamma g) gSuf wSuf' fSuf'
                           
      -> word ++ wSuf = word' ++ wSuf'
                                      
      ->  word = word'
          /\ wSuf = wSuf'
          /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun fPre =>
               forall x
                      gPre wPre wPre' fPre'
                      gSuf wSuf wSuf' fSuf fSuf',
                 
                 In (x, gPre ++ gSuf) (productions g)
                    
                 -> (@derivesGamma g) gPre wPre fPre
                 -> (@derivesGamma g) gPre wPre' fPre'
                                      
                 -> (@derivesGamma g) gSuf wSuf fSuf
                 -> (@derivesGamma g) gSuf wSuf' fSuf'

                 -> wPre ++ wSuf = wPre' ++ wSuf'
                                      
                 -> wPre = wPre'
                    /\ wSuf = wSuf'
                    /\ fSuf = fSuf').
  - intros.
    inv H0; inv H1.
    + inv H4.
      repeat (split; auto).
    + inv H5.
      
  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with (wSuf := nil)
                     (wSuf' := nil) in H1; eauto.
    + destruct H3.
      destruct H7.
      subst.
      split; auto.
    + econstructor.
    + econstructor.
    + simpl.
    + destruct H1.
      subst.
      apply suffixes_eq in H4.
      subst.
      repeat (split; auto).
    + admit.
    
  - intros.
    inv H0; inv H1.
    repeat (split; auto).

  - intros.
    inv H0; inv H1.
    pose proof H8 as H8'.
    eapply IHtr0 in H8; eauto.
    + destruct H8.
      subst.
    
    eapply IHtr0 with
        (wPre := wPre ++ prefix)
        (wPre' := wPre' ++ prefix0) in H8; eauto.
    + destruct H8.
      destruct H0.
      subst.
      

(* Input is empty, symbol could be T or NT *)
Lemma derives_nil_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym,
      (@derivesSym g) sym [] tr
      -> (@derivesSym g) sym [] tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma,
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma [] f
                 -> (@derivesGamma g) gamma [] f'
                 -> f = f').
  - intros.
    inv H.
    inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    inv H1.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0.
    inv H1.
    auto.

  - intros.
    inv H0.
    inv H1.
    assert (prefix = []) by admit.
    assert (prefix0 = []) by admit.
    assert (suffix = []) by admit.
    assert (suffix0 = []) by admit.
    subst.
    assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
    rewrite H0 in H.
    rewrite app_assoc in H.
    erewrite IHtr; eauto.
    erewrite IHtr0; eauto.
Admitted.

Lemma derivesGamma_nil_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall f f' x pre gamma,
      In (x, pre ++ gamma) (productions g)
      -> (@derivesGamma g) gamma [] f
      -> (@derivesGamma g) gamma [] f'
      -> f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall tr' sym,
                (@derivesSym g) sym [] tr
                -> (@derivesSym g) sym [] tr'
                -> tr = tr').

  - intros.
    inv H.
    inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    inv H1.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHf; eauto.

  - intros.
    inv H0.
    inv H1.
    auto.

  - intros.
    inv H0.
    inv H1.
    assert (prefix = []) by admit.
    assert (prefix0 = []) by admit.
    assert (suffix = []) by admit.
    assert (suffix0 = []) by admit.
    subst.
    assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
    rewrite H0 in H.
    rewrite app_assoc in H.
    erewrite IHf; eauto.
    erewrite IHf0; eauto.
Admitted.

Lemma derives_cons_T_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' y word word',
      (@derivesSym g) (T y) word tr
      -> (@derivesSym g) (T y) word' tr'
      -> tr = tr' /\ word = word'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr; intros.
  - inv H.
    inv H0.
    split; auto.
  - inv H.
Qed.


Lemma prefixes_eq :
  forall (suf pre pre' : list string),
    app pre suf = app pre' suf
    -> pre = pre'.
Proof.
  induction suf; intros; simpl in *.
  - repeat rewrite app_nil_r in H.
    auto.
  - assert (a :: suf = app [a] suf) by auto.
    repeat rewrite H0 in H.
    repeat rewrite app_assoc in H.
    apply IHsuf in H.
    apply app_inj_tail in H.
    destruct H.
    auto.
Qed.

Lemma suffixes_eq :
  forall (pre suf suf' : list string),
    app pre suf = app pre suf'
    -> suf = suf'.
Proof.
  induction pre; intros; simpl in *.
  - auto.
  - inv H.
    apply IHpre; auto.
Qed.

Lemma derives_det :
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
      (P0 := fun f =>
               forall f' gamma word,
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  - intros.
    inv H; inv H0; auto.
    inv H1.
  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    erewrite IHtr; eauto.

  - intros.
    inv H; inv H0; auto.

  - intros.
    inv H; inv H0.

(* Here's what we really want to prove *)
Lemma derives_det :
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
      (P0 := fun f =>
               forall f' x pre gamma word,
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0; inv H1.
    auto.

  - intros.
    inv H0; inv H1.
    destruct hdSym as [y | x2].
    + inv H6; inv H4.
      inv H3.
      assert (T y :: tlSyms = [T y] ++ tlSyms) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      erewrite IHtr0; eauto.
    + (* here, we're going to get stuck because we don't know
         whether prefix = prefix0. It would help if we knew
         that prefix and prefix0 shared the first lookahead
         token *)
Abort.

(* This gets us almost all the way there, but proving that
   gamma = gamma0 is the problem. We need to change the
   derivesSym hypothesis so that it talks about a symbol
   in the middle of some right-hand side *)
Lemma derives_det' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym pre pre' suf suf',
      (@derivesSym g) sym pre tr
      -> (@derivesSym g) sym pre' tr'
      -> pre ++ suf = pre' ++ suf'
      -> pre = pre' /\ suf = suf' /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gamma pre pre' suf suf',
                 In (x, gPre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma pre f
                 -> (@derivesGamma g) gamma pre' f'
                 -> pre ++ suf = pre' ++ suf'
                 -> pre = pre' /\ suf = suf' /\ f = f').
  
  - intros.
    inv H; inv H0.
    + inv H1.
      repeat (split; auto).
    + inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    rename s into x.
    (*
    assert (gamma0 = gamma).
    { destruct pre as [| ptok ptoks]; simpl in *.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + apply derivesGamma_nil_nullable in H0.
          apply derivesGamma_nil_nullable in H8.
          assert ((@isLookaheadFor g) EOF (NT x) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x) gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          apply Hcom in H2; apply Hcom in H3.
          destruct H2 as [laMap [Hsf Hlf]].
          destruct H3 as [laMap' [Hsf' Hlf']].
          congruence.
        + admit.
      *)      

    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H2 in H.
    eapply IHtr in H0; eauto.
    destruct H0.
    destruct H3.
    subst; repeat (split; auto).
          
  - intros.
    inv H0; inv H1; auto.

  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + destruct f' as [| tr' f'].
      * inv H1.
      * inv H0; inv H1.
        repeat rewrite <- app_assoc in H2.
        assert (sym :: syms = [sym] ++ syms) by auto.
        rewrite H0 in H.
        rewrite app_assoc in H.
        eapply IHtr with (pre := prefix) in H6; eauto.
        destruct H6.
        destruct H3.
        subst.
        eapply IHtr0 with (pre := suffix) in H10; eauto.
        destruct H10.
        destruct H4.
        subst.
        repeat (split; auto).
Admitted.

  
    
(*    
(* maybe get rid of the rem stuff *)
Lemma derivesGamma_det' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall f f' x gPre gSuf word word' rem rem',
      In (x, gPre ++ gSuf) (productions g)
      -> (@derivesGamma g) gSuf word f
      -> (@derivesGamma g) gSuf word' f'
      -> word ++ rem = word' ++ rem'
      -> word = word' /\ f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction f using forest_mutual_ind with
      (P := fun tr =>
              forall tr' x sym
                     gPre gSuf
                     wPre wPre'
                     wSuf wSuf'
                     f f'
                     rem rem',
                In (x, gPre ++ sym :: gSuf) (productions g)
                -> (@derivesSym g) sym wPre tr
                -> (@derivesSym g) sym wPre' tr'
                -> (@derivesGamma g) gSuf wSuf f
                -> (@derivesGamma g) gSuf wSuf' f'
                -> wPre ++ rem = wPre' ++ rem'
                -> wPre = wPre' /\ tr = tr').

  - intros.
    inv H0; inv H1.
    + inv H4.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    rename s into x2.
    assert (gamma0 = gamma).
    { destruct wPre as [| ptok ptoks]; simpl in *.
      - destruct wPre' as [| ptok' ptoks']; simpl in *.
        + apply derivesGamma_nil_nullable in H11.
          apply derivesGamma_nil_nullable in H1.
          assert ((@isLookaheadFor g) EOF (NT x2) gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              eapply FoNu.
              econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x2) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              eapply FoNu.
              econstructor; eauto. }
          apply Hcom in H5; apply Hcom in H6.
          destruct H5 as [laMap [Hsf Hlf]].
          destruct H6 as [laMap' [Hsf' Hlf']].
          congruence.
        + destruct wSuf as [| stok stoks]; simpl in *.
          * apply derivesGamma_nil_nullable in H11.
            apply derivesGamma_nil_nullable in H2.
            assert ((@isLookaheadFor g) EOF (NT x2) gamma).
            { unfold isLookaheadFor.
              right.
              split.
              - constructor; auto.
              - constructor; auto.
                eapply FoLeft.
                econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x2) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              eapply FoNu.
              econstructor; eauto. }destruct 
          * inv H4.
            inv H2.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + inv H2.
        + inv H1.
          apply derivesGamma_cons_firstGamma in H0.
          apply derivesGamma_cons_firstGamma in H9.
          assert ((@isLookaheadFor g) (LA ptok') (NT x) gamma).
          { unfold isLookaheadFor.
            left.
            constructor; auto. }
          assert ((@isLookaheadFor g) (LA ptok') (NT x) gamma0).
          { unfold isLookaheadFor.
            left.
            constructor; auto. }
          apply Hcom in H1; apply Hcom in H3.
          destruct H1 as [laMap [Hsf Hlf]].
          destruct H3 as [laMap' [Hsf' Hlf']].
          congruence. }
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHf in H1; eauto.
    + destruct H1.
      destruct H5.
      subst.
      repeat (split; auto).
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H5 in H0.
      eauto.

  - intros.
    inv H0; inv H1; auto.

  - intros.
    inv H0; inv H1.
    eapply IHf with (wSuf := suffix)
                    (wSuf' := suffix0)
                    (rem := rem)
                    (rem' := rem') in H4; eauto. 
    + destruct H4.
      subst.
      eapply IHf0 with (rem := rem)
                       (rem' := rem') in H9; eauto.
      * destruct H9.
        destruct H1.
        subst.
        repeat (split; auto).
      * assert (hdSym :: tlSyms = [hdSym] ++ tlSyms) by auto.
        rewrite H0 in H.
        rewrite app_assoc in H.
        eauto.
      * repeat rewrite <- app_assoc in H2.
        apply suffixes_eq in H2.
        auto.
    + repeat rewrite <- app_assoc in H2.
      auto.
Admitted.
*)

Lemma derivesGamma_det' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gSuf x gPre wPre wPre' wSuf wSuf' f f',
      In (x, gPre ++ gSuf) (productions g)
      -> (@derivesGamma g) gSuf wPre f
      -> (@derivesGamma g) gSuf wPre' f'
      -> wPre ++ wSuf = wPre' ++ wSuf'
      -> wPre = wPre' /\ wSuf = wSuf' /\ f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction gSuf as [| sym syms].
  - intros.
    inv H0; inv H1; simpl in *.
    subst.
    repeat (split; auto).
  - intros.
    destruct f as [| tr f].
    + inv H0.
    + destruct f' as [| tr' f'].
      * inv H1.
      * inv H0; inv H1.
        destruct sym as [y | x2].
        -- inv H7; inv H6.
           inv H2.
           eapply IHsyms with (wPre := suffix)
                              (wSuf := wSuf)
                              (wPre' := suffix0)
                              (wSuf' := wSuf') in H10; eauto.
           ++ destruct H10.
              destruct H2.
              subst.
              repeat (split; auto).
           ++ assert (T y :: syms = [T y] ++ syms) by auto.
              rewrite H0 in H.
              rewrite app_assoc in H.
              eauto.
        -- inv H7.
           inv H6.
           inv H1.
           inv H3.
           { destruct prefix as [| ptok ptoks]; simpl in *.
             - destruct prefix0 as [| ptok' ptoks']; simpl in *.
               + apply derivesGamma_nil_nullable in H4.
                 apply derivesGamma_nil_nullable in H5.
                 assert ((@isLookaheadFor g) EOF (NT x2) gamma).
                 { unfold isLookaheadFor.
                   right.
                   split.
                   - constructor; auto.
                   - constructor; auto.
                     eapply FoNu; eauto.
                     econstructor; eauto. }
                 assert ((@isLookaheadFor g) EOF (NT x2) gamma0).
                 { unfold isLookaheadFor.
                   right.
                   split.
                   - constructor; auto.
                   - constructor; auto.
                     eapply FoNu; eauto.
                     econstructor; eauto. }
                 apply Hcom in H3; apply Hcom in H6.
                 destruct H3 as [laMap [Hsf Hlf]].
                 destruct H6 as [laMap' [Hsf' Hlf']].
Abort.
                   
          
(* Here we're trying the "sym in the middle of an RHS"
   strategy *)
Lemma derives_det'' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x gPre sym gSuf
              pre pre'
              suf suf'
              f f',
      In (x, gPre ++ sym :: gSuf) (productions g)
      -> (@derivesSym g) sym pre tr
      -> (@derivesSym g) sym pre' tr'
      -> (@derivesGamma g) gSuf suf f
      -> (@derivesGamma g) gSuf suf' f'
      -> pre ++ suf = pre' ++ suf'
      -> pre = pre' /\ suf = suf' /\ tr = tr'.
(* add the fact that f and f' are equal in the conclusion? *)
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gamma gSuf
                      pre pre'
                      suf suf'
                      fSuf fSuf',
                 In (x, gPre ++ gamma ++ gSuf) (productions g)
                 -> (@derivesGamma g) gamma pre f
                 -> (@derivesGamma g) gamma pre' f'
                 -> (@derivesGamma g) gSuf suf fSuf
                 -> (@derivesGamma g) gSuf suf' fSuf'
                 -> pre ++ suf = pre' ++ suf'
                 -> pre = pre' /\ suf = suf' /\ f = f'
                    /\ fSuf = fSuf').

  - intros.
    inv H0; inv H1.
    + inv H4.
      repeat (split; auto).
    + inv H5.

  - intros.
    inv H0; inv H1.
    inv H5; inv H6.
    rename s into x2.
    assert (gamma0 = gamma).
    { 
      destruct pre as [| ptok ptoks]; simpl in *.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + apply derivesGamma_nil_nullable in H1.
          apply derivesGamma_nil_nullable in H11.
          assert ((@isLookaheadFor g) EOF (NT x2) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x2) gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          apply Hcom in H5; apply Hcom in H6.
          destruct H5 as [laMap [Hsf Hlf]].
          destruct H6 as [laMap' [Hsf' Hlf']].
          congruence.
        + subst.
          assert ((@isLookaheadFor g) (LA ptok')
                                      (NT x2)
                                      gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
              apply derivesGamma_nil_nullable in H11.
              auto.
            - constructor; auto.
              eapply FoRight with
                  (x1 := x)
                  (prefix := gPre)
                  (suffix := gSuf); eauto.
              apply derivesGamma_cons_firstGamma in H2.
              auto. }
          assert ((@isLookaheadFor g) (LA ptok')
                                      (NT x2)
                                      gamma0).
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H1.
            auto. }
          apply Hcom in H4; apply Hcom in H5.
          destruct H4 as [laMap [Hsf Hlf]].
          destruct H5 as [laMap' [Hsf' Hlf']].
          congruence.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + subst.
          assert ((@isLookaheadFor g) (LA ptok)
                                      (NT x2)
                                      gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
              apply derivesGamma_nil_nullable in H1.
              auto.
            - constructor; auto.
              eapply FoRight with
                  (x1 := x)
                  (prefix := gPre)
                  (suffix := gSuf); eauto.
              apply derivesGamma_cons_firstGamma in H3.
              auto. }
          assert ((@isLookaheadFor g) (LA ptok)
                                      (NT x2)
                                      gamma).
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H11.
            auto. }
          apply Hcom in H4; apply Hcom in H5.
          destruct H4 as [laMap [Hsf Hlf]].
          destruct H5 as [laMap' [Hsf' Hlf']].
          congruence.
        + inv H4.
          assert ((@isLookaheadFor g) (LA ptok')
                                      (NT x2)
                                      gamma).
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H11.
            auto. }
          assert ((@isLookaheadFor g) (LA ptok')
                                      (NT x2)
                                      gamma0).
          { unfold isLookaheadFor.
            left.
            constructor; auto.
            apply derivesGamma_cons_firstGamma in H1.
            auto. }
          apply Hcom in H4; apply Hcom in H5.
          destruct H4 as [laMap [Hsf Hlf]].
          destruct H5 as [laMap' [Hsf' Hlf']].
          congruence. }
    subst.
    
           
    eapply IHtr with (gamma := [NT x2])
                     (pre := pre)
                     (pre' := pre')
                     (suf := suf)
                     (suf' := suf')
                     (f' := f1) in H; eauto.
    + destruct H.
      destruct H5.
      destruct H6.
      subst.
      repeat (split; auto).
    + admit.
    + admit.
    
  - intros.
    inv H0; inv H1; auto.
    simpl in *.
    subst.
    admit.
    
  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + destruct f' as [| tr' f'].
      * inv H1.
      * inv H0; inv H1.
        repeat rewrite <- app_assoc in H2.
        eapply (IHtr tr' x gPre sym syms prefix prefix0
                     (suffix ++ suf) (suffix0 ++ suf')
                     _ _) in H8; eauto.
        -- destruct H8.
           destruct H1.
           subst.
           repeat rewrite <- app_assoc in H4.
           assert (suffix ++ suf = suffix0 ++ suf') by admit.
           (* this is an easy prefix/suffix fact *)
           eapply IHtr0 with (pre := suffix)
                             (pre' := suffix0)
                             (suf := suf)
                             (suf' := suf') in H12; eauto.
           ++ destruct H12.
              destruct H5.
              destruct H6.
              subst.
Abort.

Lemma two_gammas :
  forall tbl g,
    isParseTableFor tbl g
    -> forall x gamma gamma' word word' f f',
      In (x, gamma) (productions g)
      -> In (x, gamma') (productions g)
      -> (@derivesGamma g) gamma word f
      -> (@derivesGamma g) gamma' word' f'
      -> (peek word = peek word' -> gamma = gamma')
         /\ (peek word <> peek word' -> gamma <> gamma').
Proof.
Admitted.

Lemma derives_det''' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym pre pre' suf suf',
      (@derivesSym g) sym pre tr
      -> (@derivesSym g) sym pre' tr'
      -> pre ++ suf = pre' ++ suf'
      -> peek (pre ++ suf) = peek (pre' ++ suf')
      -> pre = pre' /\ suf = suf' /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gamma pre pre' suf suf',
                 In (x, gPre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma pre f
                 -> (@derivesGamma g) gamma pre' f'
                 -> pre ++ suf = pre' ++ suf'
                 -> peek (pre ++ suf) = peek (pre' ++ suf')
                 -> pre = pre' /\ suf = suf' /\ f = f').

  - intros.
    inv H; inv H0.
    + inv H1.
      repeat (split; auto).
    + inv H3.

  - intros.
    inv H; inv H0.
    inv H3; inv H4.
    rename s into x.
    assert (gamma0 = gamma).
    { destruct pre as [| ptok ptoks]; simpl in *.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + subst.
          apply derivesGamma_nil_nullable in H9.
          apply derivesGamma_nil_nullable in H0.
          assert ((@isLookaheadFor g) EOF (NT x) gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              eapply FoNu.
              econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              eapply FoNu.
              econstructor; eauto. }
          apply Hcom in H1; apply Hcom in H3.
          destruct H1 as [laMap [Hsf Hlf]].
          destruct H3 as [laMap' [Hsf' Hlf']].
          congruence.
        + destruct suf as [| stok stoks]; simpl in *.
          * inv H2.
          * inv H2.
            
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + inv H2.
        + inv H1.
          apply derivesGamma_cons_firstGamma in H0.
          apply derivesGamma_cons_firstGamma in H9.
          assert ((@isLookaheadFor g) (LA ptok') (NT x) gamma).
          { unfold isLookaheadFor.
            left.
            constructor; auto. }
          assert ((@isLookaheadFor g) (LA ptok') (NT x) gamma0).
          { unfold isLookaheadFor.
            left.
            constructor; auto. }
          apply Hcom in H1; apply Hcom in H3.
          destruct H1 as [laMap [Hsf Hlf]].
          destruct H3 as [laMap' [Hsf' Hlf']].
          congruence. }
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H3 in H.
    eapply IHtr in H0; eauto.
    destruct H0.
    destruct H4.
    subst.
    repeat (split; auto).

  - intros.
    inv H0; inv H1; auto.

  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + destruct f' as [| tr' f'].
      * inv H1.
      * inv H0; inv H1.
        destruct (prefix ++ suffix) eqn:Hpre; simpl in *.
        -- destruct (prefix0 ++ suffix0) eqn:Hpre0; simpl in *.
           ++ subst.
              assert (prefix = nil) by admit.
              assert (prefix0 = nil) by admit.
              assert (suffix = nil) by admit.
              assert (suffix0 = nil) by admit.
              subst.
              eapply IHtr in H7; eauto.
              destruct H7.
              destruct H1.
              subst.
              eapply IHtr0 with (suf := nil)
                                (suf' := nil) in H11; eauto.
              ** destruct H11.
                 destruct H4.
                 subst.
                 repeat (split; auto).
              ** admit.
           ++ inv H3.
        -- destruct (prefix0 ++ suffix0) eqn:Hpre0; simpl in *.
           ++ inv H3.
           ++ inv H3.
              destruct prefix; destruct suffix; simpl in *.
              ** inv Hpre.
              ** inv Hpre.
Abort.                


(* This gets us almost all the way there, but proving that
   gamma = gamma0 is the problem. We need to change the
   derivesSym hypothesis so that it talks about a symbol
   in the middle of some right-hand side *)
Lemma derives_det' :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym pre pre' suf suf',
      (@derivesSym g) sym pre tr
      -> (@derivesSym g) sym pre' tr'
      -> pre ++ suf = pre' ++ suf'
      -> pre = pre' /\ suf = suf' /\ tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x gPre gamma pre pre' suf suf',
                 In (x, gPre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma pre f
                 -> (@derivesGamma g) gamma pre' f'
                 -> pre ++ suf = pre' ++ suf'
                 -> pre = pre' /\ suf = suf' /\ f = f').
  
  - intros.
    inv H; inv H0.
    + inv H1.
      repeat (split; auto).
    + inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    rename s into x.
    (*
    assert (gamma0 = gamma).
    { destruct pre as [| ptok ptoks]; simpl in *.
      - destruct pre' as [| ptok' ptoks']; simpl in *.
        + apply derivesGamma_nil_nullable in H0.
          apply derivesGamma_nil_nullable in H8.
          assert ((@isLookaheadFor g) EOF (NT x) gamma0).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          assert ((@isLookaheadFor g) EOF (NT x) gamma).
          { unfold isLookaheadFor.
            right.
            split.
            - constructor; auto.
            - constructor; auto.
              econstructor.
              econstructor; eauto. }
          apply Hcom in H2; apply Hcom in H3.
          destruct H2 as [laMap [Hsf Hlf]].
          destruct H3 as [laMap' [Hsf' Hlf']].
          congruence.
        + admit.
      *)      

    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H2 in H.
    eapply IHtr in H0; eauto.
    destruct H0.
    destruct H3.
    subst; repeat (split; auto).
          
  - intros.
    inv H0; inv H1; auto.

  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + destruct f' as [| tr' f'].
      * inv H1.
      * inv H0; inv H1.
        repeat rewrite <- app_assoc in H2.
        assert (sym :: syms = [sym] ++ syms) by auto.
        rewrite H0 in H.
        rewrite app_assoc in H.
        eapply IHtr with (pre := prefix) in H6; eauto.
        destruct H6.
        destruct H3.
        subst.
        eapply IHtr0 with (pre := suffix) in H10; eauto.
        destruct H10.
        destruct H4.
        subst.
        repeat (split; auto).
Admitted.
           
        
        
    
  

Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym' /\ word = word')
         /\ (tr <> tr' -> sym <> sym' \/ word <> word').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma gamma' word word',
                 In (x, pre ++ gamma) (productions g)
                 -> In (x, pre ++ gamma') (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (f = f' ->  gamma = gamma' /\ word = word')
                    /\ (f <> f' -> gamma <> gamma'
                                   \/ word <> word')).

  - intros.
    inv H.
    + inv H0.
      * split.
        -- intros; split; congruence.
        -- intros.
           left.
           unfold not; intros.
           inv H0.
           congruence.
      * inv H.
        split; intros.
        -- congruence.
        -- left.
           congruence.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H1.
    split; intros.
    + congruence.
    + left.
      congruence.
    + inv H1; inv H.
      split; intros.
      * inv H.
        eapply IHtr with (pre := nil) (gamma := gamma) in H0;
          eauto.
        destruct H0.
        destruct H; auto.
      * destruct (forest_eq_dec f f0).
        -- subst.
           
        
          
        

    
Qed.      
        

(* This time, we relax the restriction that the two words be
   equal, and just require them to share a lookahead token *)
Lemma derives_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
      -> peek word = peek word'
      -> tr = tr' /\ word = word'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma word,
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 ->  f = f').
  - intros.
    inv H; inv H0; auto.
    inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    assert (gamma0 = gamma) by admit. (* get this from LL(1) *)
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H2 in H.
    split.
    + erewrite IHtr; auto.
      * eauto.
      * eauto.
      * (* we're stuck, because the IH still requires the two
           words to be the same. Let's try relaxing that
           restriction. *)
Abort.




    

Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr
      -> sym = sym' /\ word = word'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall x pre gamma gamma' word word',
                 In (x, pre ++ gamma) (productions g)
                 -> In (x, pre ++ gamma') (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f
                 ->  gamma = gamma' /\ word = word').

  - intros.
    inv H.
    + inv H0.
      * split; auto.
      * inv H.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H; inv H1.
    eapply IHtr with (gamma := gamma)
                     (word := word) in H7; auto.
    + destruct H7.
      split; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H in H5.
      eauto.
    + auto.
  - intros.
    inv H1; inv H2.
    split; auto.
    
  - intros.
    inv H1; inv H2.
    eapply IHtr with
        (sym := hdSym) (word := prefix) in H6; auto.
    destruct H6; subst.
    eapply IHtr0 with
        (gamma := tlSyms) (word := suffix) in H9; auto.
    + destruct H9.
      subst; split; auto.
    + assert (hdSym0 :: tlSyms = [hdSym0] ++ tlSyms) by auto.
      rewrite H1 in H.
      rewrite app_assoc in H.
      eauto.
    + assert (hdSym0 :: tlSyms0 = [hdSym0] ++ tlSyms0) by auto.
      rewrite H1 in H0.
      rewrite app_assoc in H0.
      auto.
Qed.      





Lemma derives_cons_NT_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x tok toks toks',
      (@derivesSym g) (NT x) (tok :: toks) tr
      -> (@derivesSym g) (NT x) (tok :: toks') tr'
      -> tr = tr' /\ toks = toks'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma tok toks toks',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma (tok :: toks) f
                 -> (@derivesGamma g) gamma (tok :: toks') f'
                 -> f = f' /\ toks = toks').
  - intros.
    inv H.
    inv H2.
    
  - intros.
    inv H.
    inv H2.
    inv H0.
    inv H1.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    eapply IHtr in H0; eauto.
    destruct H0.
    subst.
    split; auto.

  - intros.
    inv H0.
    
  - intros.
    inv H0.
    inv H1.
    destruct hdSym as [y | x2].
    + destruct prefix as [| ptok ptoks]; simpl in *.
      * inv H6.
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- inv H5.
        -- inv H4.
           inv H2.
           inv H5.
           inv H6.
           simpl in *.
           
           
           split; auto.
    + destruct prefix as [| ptok ptoks]; simpl in *.
      * destruct prefix0 as [| ptok' ptoks']; simpl in *.
        -- eapply derives_nil_det with (tr := tr) in H3; eauto.
           subst.
           split; auto.
        -- destruct suffix0 as [| stok stoks]; simpl in *.
           ++ 
      
           
           

    
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma tok toks toks',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma (tok :: toks) f
                 -> (@derivesGamma g) gamma (tok :: toks') f'
                 -> f = f' /\ toks = toks').

  - intros.
    inv H.
    + inv H0.
      split; auto.
    + inv H1.

  - intros.
    inv H.
    inv H1.
    inv H0.
    inv H1.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    eapply IHtr in H0; eauto.
    destruct H0.
    subst.
    split; auto.

  - intros.
    inv H0.

  - intros.
    inv H0.
    inv H1.
    destruct hdSym as [y | x2].
    + destruct prefix.
      * inv H6.
      * destruct prefix0.
        -- inv H5.
        -- inv H4.
           eapply IHtr with (toks := []) in H5.
           ++ destruct H5.
              subst.
      * inv H5.
      * simpl in *.
        inv H4.
      
    
Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
      -> peek word = peek word'
      -> tr = tr' /\ word = word'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma word word',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word' f'
                 -> peek word = peek word'
                 -> f = f' /\ word = word').
  - intros.
    inv H; inv H0; auto.
    inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    assert (gamma0 = gamma) by admit.
    subst.
    eapply IHtr with (word := word) in H0; eauto.
    + destruct H0; subst; split; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H2 in H.
      eauto.

  - intros.
    inv H0; inv H1; auto.

  - intros.

    
        










    
    
Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> peek word = peek word'
      -> (tr = tr' -> sym = sym' /\ word = word')
         /\ (tr <> tr' -> sym <> sym').
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' gamma gamma' word word',
                 (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> peek word = peek word'
                 -> (f = f' -> gamma = gamma' /\ word = word')
                    /\ (f <> f' -> gamma <> gamma')).
  
  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H.
           split; auto.
        -- congruence.
      * inv H.
        split; intros; congruence.
    + inv H2.

  - intros.
    inv H.
    inv H2.
    inv H0.
    + split; intros; congruence.
    + inv H.
      pose proof H2 as H2'.
      eapply IHtr with (gamma := gamma) (word := word)
        in H2; eauto.
      destruct H2.
      split; intros.
      * inv H3.
        destruct H; auto.
      * unfold not; intros.
        inv H4.
        assert (gamma0 = gamma) by admit.
        subst.
        destruct (forest_eq_dec f f0).
        -- subst.
           congruence.
        -- apply H2 in n.
           congruence.

  - intros.
    inv H; inv H0.
    + split; intros; auto.
    + split; intros; congruence.

  - intros.
    inv H; inv H0.
    + split; intros; congruence.
    + split; intros.
      * inv H0.
        destruct prefix as [| ptok ptoks]; simpl in *.
        -- destruct prefix0 as [| ptok' ptoks']; simpl in *.
           ++ destruct suffix as [| stok stoks]; simpl in *.
              ** simpl in *.
                 destruct suffix0 as [| stok' stoks'];
                   simpl in *.
                 --- eapply IHtr0 with
                         (gamma := tlSyms) in H2; eauto.
                     destruct H2.
                     destruct H0; auto.
                     subst.
                     eapply IHtr with (sym := hdSym)
                       in H; eauto.
                     destruct H.
                     destruct H; auto.
                     subst.
                     split; auto.
                 --- inv H1.
              ** destruct suffix0 as [| stok' stoks'];
                   simpl in *.
                 --- inv H1.
                 --- inv H1.
                     eapply IHtr0 with
                         (gamma := tlSyms) in H2; eauto.
                     destruct H2.
                     destruct H0; auto.
                     inv H2.
                     subst.
                     eapply IHtr with
                         (sym := hdSym) in H; eauto.
                     destruct H.
                     destruct H; auto.
                     subst.
                     split; auto.
           ++ destruct suffix as [| stok stoks]; simpl in *.
              ** inv H1.
              ** inv H1.
                 destruct suffix0 as [| stok' stoks'];
                   simpl in *.
                 --- eapply IHtr0 with (gamma := tlSyms)
                     in H2; eauto.
                     +++ destruct H2.
                         destruct H0; auto.
                         inv H2.
                     +++ eapply IHtr

             
  - intros.
    inv H1; inv H2.
    + split; intros; congruence.
    + split; intros.
      * inv H2.
        eapply IHtr with (sym := hdSym) in H3; eauto.
        -- destruct H3.
           destruct H2; auto.
           eapply IHtr0 with (gamma := tlSyms) in H5; eauto.
           ++ destruct H5.
              destruct H2; auto.
           ++ assert (hdSym :: tlSyms = [hdSym] ++ tlSyms)
               by auto.
              rewrite H2 in H.
              rewrite app_assoc in H.
              eauto.
           ++ assert (hdSym :: tlSyms0 = [hdSym] ++ tlSyms0)
               by auto.
              rewrite H2 in H0.
              rewrite app_assoc in H0.
              auto.
           ++ 

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word' tr'
      -> peek word = peek word'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma word word',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word' f'
                 -> f = f').
  - intros.
    inv H; inv H0; auto.
    inv H2.

  - intros.
    inv H; inv H0.
    inv H2; inv H3.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H2 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0; inv H1; auto.

  - intros.
    inv H0; inv H1.
    destruct hdSym as [y | x2].
    + inv H3; inv H6.
      assert (T y :: tlSyms = [T y] ++ tlSyms) by auto.
      rewrite H0 in H.
      rewrite app_assoc in H.
      erewrite IHtr0; eauto.
    + 
    destruct prefix as [| ptok ptoks].
    + destruct prefix0 as [| ptok' ptoks']; simpl in *.
      * eapply IHtr in H3; eauto.
        subst.
        eapply IHtr0 in H8; eauto.
        subst.
        auto.
      * (* first/follow *)
        inv H6; inv H3.
        inv H; inv H2.
        destruct suffix as [| stok stoks].
        -- inv H1.
        -- simpl in *.
           inv H1.
           



        
           

    

Lemma if_trees_eq_then_syms_and_words_eq :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr
      -> sym = sym' /\ word = word'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall x pre gamma gamma' word word',
                 In (x, pre ++ gamma) (productions g)
                 -> In (x, pre ++ gamma') (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f
                 ->  gamma = gamma' /\ word = word').

  - intros.
    inv H.
    + inv H0.
      * split; auto.
      * inv H.
    + inv H1.

  - intros.
    inv H; inv H0.
    inv H; inv H1.
    eapply IHtr with (gamma := gamma)
                     (word := word) in H7; auto.
    + destruct H7.
      split; auto.
    + assert (gamma = [] ++ gamma) by auto.
      rewrite H in H5.
      eauto.
    + auto.
  - intros.
    inv H1; inv H2.
    split; auto.
    
  - intros.
    inv H1; inv H2.
    eapply IHtr with
        (sym := hdSym) (word := prefix) in H6; auto.
    destruct H6; subst.
    eapply IHtr0 with
        (gamma := tlSyms) (word := suffix) in H9; auto.
    + destruct H9.
      subst; split; auto.
    + assert (hdSym0 :: tlSyms = [hdSym0] ++ tlSyms) by auto.
      rewrite H1 in H.
      rewrite app_assoc in H.
      eauto.
    + assert (hdSym0 :: tlSyms0 = [hdSym0] ++ tlSyms0) by auto.
      rewrite H1 in H0.
      rewrite app_assoc in H0.
      auto.
Qed.      
    
    
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr sym sym' word word',
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym' word' tr'
      -> (tr = tr' -> sym = sym' /\ word = word').
         (* /\ (tr <> tr' -> sym <> sym'). *)
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma gamma' word word',
                 In (x, pre ++ gamma) (productions g)
                 -> In (x, pre ++ gamma') (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma' word' f'
                 -> (f = f' -> gamma = gamma' /\ word = word')
                    /\ (f <> f' -> gamma <> gamma')).

  - intros.
    inv H.
    + inv H0.
      * split; intros.
        -- inv H; split; auto.
        -- congruence.
      * inv H; split; intros; congruence.
    + inv H1.
        
  - intros.
    inv H.
    inv H1.
    inv H0.
    + split; intros; congruence.
    + inv H.
      destruct (forest_eq_dec f f0).
      * subst.
        assert (gamma = [] ++ gamma) by auto.
        rewrite H in H6.
        eapply IHtr with (gamma := gamma) in H1; auto.
        -- split; intros.
           ++ inv H2.
              destruct H1.
              destruct H1; auto.
              split; eauto.
           ++ unv
           subst.
           split; intros.
           ++ inv H1; split; auto.
           ++ unfold not; intros.
              inv H3.
              apply H1.
              auto.
        -- assert (gamma0 = [] ++ gamma0) by auto.
           rewrite H2 in H0.
           auto.
      split; intros.
      * inv H.
        split; auto.
      * unfold not; intros.
        inv H2.
        apply H; clear H.
        assert (gamma0 = gamma) by admit.
        subst.
        assert (gamma = [] ++ gamma) by auto.
        rewrite H in H0.
        eapply IHtr with (gamma := gamma) in H1; eauto.
        destruct H1.
        destruct (forest_eq_dec f f0).
        -- subst; auto.
        -- simpl in *.
           apply H2 in n.
           congruence.

  - intros.
    inv H1; inv H2; split; intros; auto; try congruence.

  - intros.
    inv H1; inv H2; split; intros; try congruence.
    + inv H2.
      
        
        
        
      


Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall x pre gamma word f',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').
  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H1 in H.
    erewrite IHtr; eauto.

  - intros.
    inv H0; inv H1; auto.

  - intros.
    inv H0.
    


Lemma derivesProd_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr x gamma word,
      (@derivesProd g) x gamma word tr
      -> forall tr',
          (@derivesProd g) x gamma word tr'
          -> tr = tr'.
Proof.
  intros tbl g Htbl tr x gamma word Hderp.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction Hderp using derivesProd_mut_ind with
      (P := fun x gamma word tr
                (pf : (@derivesProd g) x gamma word tr) =>
              forall tr',
                (@derivesProd g) x gamma word tr'
                -> tr = tr')
      (P0 := fun gSuf wSuf fSuf
                 (pf : (@derivesGamma g) gSuf wSuf fSuf) =>
               forall x gPre fSuf',
                 In (x, gPre ++ gSuf) (productions g)
                 -> (forall wPre fPre fPre',
                        (@derivesGamma g) gPre wPre fPre
                        -> (@derivesGamma g) gPre wPre fPre'
                        -> fPre = fPre')
                 -> (@derivesGamma g) gSuf wSuf fSuf'
                 -> fSuf = fSuf')
      (P1 := fun sym word tr
                 (pf : (@derivesSym g) sym word tr) =>
                  forall tr',
                    (@derivesSym g) sym word tr'
                    -> tr = tr').

  - intros.
    inv H.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H in H0.
    erewrite IHHderp; eauto.
    intros.
    inv H2.
    inv H3.
    auto.

  - intros.
    rewrite app_nil_r in *.
    inv H1.
    auto.

  - intros.
    inv H1.
Abort.              

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x pre preWord preF sym word suf,
      In (x, pre ++ sym :: suf) (productions g)
      -> (@derivesGamma g) pre preWord preF
      -> (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall x pre gamma word f',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').
  - intros.
    inv H1; inv H2; auto.
    inv H3.

  - intros.
    inv H1; inv H2.
    inv H3; inv H4.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    rewrite H3 in H1.
    erewrite IHtr; eauto.

  - intros.
    inv H0; inv H1; auto.

  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + destruct sym as [y | x2].
      * inv H0; inv H1.
        inv H4; inv H6.
        inv H3.
        assert (T y :: syms = [T y] ++ syms) by auto.
        rewrite H0 in H.
        rewrite app_assoc in H.
        erewrite IHtr0; eauto.
      * destruct word as [| tok toks].
        -- 
        
    
    
      

    
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' sym word,
      (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall x pre preWord preF gamma word f',
                 In (x, pre ++ gamma) (productions g)
                 -> (@derivesGamma g) pre preWord preF
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').

  - intros.
    inv H; inv H0; auto.
    inv H1.

  - intros.
    inv H; inv H0.
    inv H1; inv H2.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = [] ++ gamma) by auto.
    erewrite IHtr with (pre := nil); eauto.
    constructor.

  - intros.
    inv H1; inv H2; auto.

  - intros.
    destruct gamma as [| sym suf].
    + inv H1.
    + destruct sym as [y | x2].
      * inv H1; inv H2.
        inv H5; inv H7.
        inv H4.
        erewrite IHtr0 with (f' := tlTrees); auto.
        -- assert (T y :: suf = [T y] ++ suf) by auto.
           rewrite H1 in H.
           rewrite app_assoc in H.
           eauto.
        -- eapply derives_app; eauto.
           repeat constructor.
        -- eauto.
        -- auto.
      * destruct word as [| tok toks].
        -- inv H1; inv H2.
           
Proof.

Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall gamma x pre preWord preF word f f',
      In (x, pre ++ gamma) (productions g)
      -> (@derivesGamma g) gamma word f
      -> (@derivesGamma g) gamma word f'
      -> (@derivesGamma g) pre preWord preF
      -> f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction gamma as [| sym syms].
  - intros.
    inv H0; inv H1; auto.
  - intros.
    destruct sym as [y | x2].
    + destruct word as [| tok toks].
      * inv H0.
        assert (prefix = nil) by admit.
        subst.
        inv H6.
      * inv H0; inv H1.
        inv H6; inv H7.
        inv H5; inv H4.
        erewrite IHsyms with (f := tlTrees)
                             (f' := tlTrees0); auto.
        -- assert (T tok :: syms = [T tok] ++ syms) by auto.
           rewrite H0 in H.
           rewrite app_assoc in H.
           eauto.
        -- eauto.
        -- auto.
        -- eapply derives_app; eauto.
           repeat constructor.
    + destruct word as [| tok toks].
      * inv H0; inv H1.
        assert (suffix = nil) by admit.
        assert (suffix0 = nil) by admit.
        subst.
        rewrite app_nil_r in *.
        subst.

        
        
      

    

    
  - intros.
    inv H0; inv H1; auto.
    assert (prefix = nil) by admit.
    assert (prefix0 = nil) by admit.
    assert (suffix = nil) by admit.
    assert (suffix0 = nil) by admit.
    subst.
    destruct hdSym as [y | x2].
    + inv H3.
    + admit.
  - intros.
    
      


    
Lemma derivesSym_det :
  forall tbl g,
    isParseTableFor tbl g
    -> forall tr tr' x pre sym suf word,
      In (x, pre ++ sym :: suf) (productions g)
      -> (@derivesSym g) sym word tr
      -> (@derivesSym g) sym word tr'
      -> tr = tr'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction tr using tree_mutual_ind with
      (P0 := fun f =>
               forall f' x pre gamma suf word,
                 In (x, pre ++ gamma ++ suf) (productions g)
                 -> (@derivesGamma g) gamma word f
                 -> (@derivesGamma g) gamma word f'
                 -> f = f').
                                       
  - intros.
    inv H0; inv H1; auto.
    inv H2.

  - intros.
    inv H0; inv H1.
    inv H2; inv H3.
    assert (gamma0 = gamma) by admit.
    subst.
    assert (gamma = nil ++ gamma ++ nil).
    { rewrite app_nil_r; auto. }
    rewrite H2 in H0.
    eapply IHtr in H0; eauto.
    subst; auto.

  - intros.
    inv H0; inv H1; auto.

  - intros.
    destruct gamma as [| sym syms].
    + inv H0.
    + inv H0; inv H1.
      
    

    
    + inv H1.
    + pose proof H1 as H1'.
      pose proof H2 as H2'.
      inv H1.
      inv H2.
      assert (sym :: syms = [sym] ++ syms) by auto.
      rewrite H1 in H.
      rewrite app_assoc in H.
      pose proof H as H'.
      eapply (IHtr0 tlTrees x (pre ++ [sym]) syms
                    (preWord ++ prefix) suffix preF) in H.
      * destruct H.
        pose proof H5.
        admit.
      * 
        apply IHtr in H5; auto.
        -- rewrite H.
           rewrite H5.
           auto.
        -- 

          
                with (preWord := preWord ++ prefix) in H.
      pose proof H as H''.
      destruct H.
      assert (appF preF (Fcons tr f) =
              appF (appF preF (Fcons tr Fnil)) f) by admit.
      rewrite H3; clear H3.
      assert (appF preF (Fcons hdTree tlTrees) =
              appF (appF preF (Fcons hdTree Fnil)) tlTrees) by admit.
      rewrite H3; clear H3.
      split.
      * rewrite H.
        rewrite H in H2.
        


      eapply IHtr0 with (preF := appF preF (Fcons hdTree Fnil))
                        (f' := tlTrees) in H.
      * destruct H.
        subst.
        assert (suffix = suffix0) by admit. (* need lemma *)
        subst.
        assert (prefix0 = prefix) by admit.
        subst.
        apply IHtr in H5; auto.
        subst.
        split; auto.
      * apply derives_app with (wPre := preWord)
                               (wSuf := prefix0); auto.
        assert (prefix0 = prefix0 ++ nil).
        { rewrite app_nil_r; auto. }
        rewrite H2.
        constructor.
        auto.
        constructor.
      * eauto.
      * eauto.

        
        assert (suffix = suffix0) by admit.
        subst.
        assert (prefix = prefix0) by admit.
        subst.
        erewrite IHtr; eauto.
      * eapply derives_app.
        -- eauto.
        -- assert (prefix = prefix ++ nil) by
              (rewrite app_nil_r; auto).
           rewrite H2.
           eapply derivesFcons; eauto.
           constructor.
      * auto.
        -- 
        
      

    rewrite H2.
    clear H1; clear H2.
    assert (appF preF (Fcons hdTree tlTrees) =
            appF preF (appF (Fcons hdTree Fnil) tlTrees)) by admit.
    rewrite H1.
    assert (appF preF (appF (Fcons hdTree Fnil) tlTrees) =
            appF (appF preF (Fcons hdTree Fnil)) tlTrees) by admit.
    rewrite H2.
    clear H1; clear H2.
    

    
Lemma derivesGamma_det : 
  forall tbl g,
    isParseTableFor tbl g
    -> forall suf x pre sym word f f',
      In (x, pre ++ sym :: suf) (productions g)
      -> (@derivesGamma g) (sym :: suf) word f
      -> (@derivesGamma g) (sym :: suf) word f'
      -> f = f'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction suf as [| sym' suf].
    apply IHsuf in 
    
      
Lemma derivesGamma_det : 
  forall tbl g,
    isParseTableFor tbl g
    -> forall sufForest sufForest'
              preGamma sufGamma
              preWord sufWord
              preForest x,
      In (x, preGamma ++ sufGamma) (productions g)
      -> (@derivesGamma g) preGamma preWord preForest
      -> (@derivesGamma g) sufGamma sufWord sufForest
      -> (@derivesGamma g) sufGamma sufWord sufForest'
      -> sufForest = sufForest'.
Proof.
  intros tbl g Htbl.
  pose proof Htbl as Htbl'.
  destruct Htbl as [Hmin Hcom].
  induction sufForest using forest_mutual_ind with
      (P := fun tr =>
              forall tr' x pre sym symWord suf sufWord sufForest sufForest',
                In (x, pre ++ sym :: suf) (productions g)
                -> (@derivesSym g) sym symWord tr
                -> (@derivesSym g) sym symWord tr'
                -> (@derivesGamma g) suf sufWord sufForest
                -> (@derivesGamma g) suf sufWord sufForest'
                -> Fcons tr sufForest = Fcons tr' sufForest').
  - intros.
    inv H0; inv H1; auto.
    + 

  - intros tr' x pre sym suf word Hin Hder Hder'.
    inv Hder; inv Hder'.
    inv H; inv H1.
    assert (gamma = gamma0) by admit.
    subst.
    admit.

  - intros sufForest' preGamma sufGamma preWord sufWord
           preForest x Hin Hderp Hders Hders'.
    inv Hders; inv Hders'; auto.

  - intros sufForest' preGamma sufGamma preWord sufWord
           preForest x Hin Hderp Hders Hders'.
    inv Hders; inv Hders'.
      

          

      
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