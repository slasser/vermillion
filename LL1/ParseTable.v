Require Import List MSets String.
Require Import FMaps Grammar Lib.Utils.
Import ListNotations.
Open Scope list_scope.

Inductive lookahead :=
| LA  : string -> lookahead
| EOF : lookahead.

(* sets and maps for lookahead tokens *)

Definition lookahead_eq_dec :
  forall (lk lk2 : lookahead),
    {lk = lk2} + {~lk = lk2}.
Proof. repeat decide equality. Defined.
  
Module MDT_Lookahead.
  Definition t := lookahead.
  Definition eq_dec := lookahead_eq_dec.
End MDT_Lookahead.

Module LookaheadAsDT := Make_UDT(MDT_Lookahead).
Module LookaheadSet := MSetWeakList.Make LookaheadAsDT.
Module LookaheadSetFacts := WFactsOn LookaheadAsDT LookaheadSet.
Module LookaheadSetEqProps := EqProperties LookaheadSet.

Module LookaheadMap := FMapWeakList.Make LookaheadAsDT.
Module LookaheadMapFacts := WFacts_fun LookaheadAsDT LookaheadMap.

Definition parse_table :=
  StringMap.t (LookaheadMap.t (list symbol)).

Definition parseTableLookup
           (x : string)
           (y : lookahead)
           (tbl : parse_table) : option (list symbol) :=
  match StringMap.find x tbl with
  | None => None
  | Some tMap => LookaheadMap.find y tMap
  end.

(* Changed nullable_sym from nonterminal to symbol *)
Inductive nullable_prod {g : grammar} :
  symbol -> list symbol -> Prop :=
| NuProd :
    forall x ys,
      In (x, ys) g.(productions)
      -> nullable_gamma ys
      -> nullable_prod (NT x) ys
with nullable_gamma {g : grammar} :
       list symbol -> Prop :=
     | NuNil :
         nullable_gamma nil
     | NuCons :
         forall x tl,
           nullable_sym (NT x)
           -> nullable_gamma tl
           -> nullable_gamma (NT x :: tl)
with nullable_sym {g : grammar} :
       symbol -> Prop :=
     | NuSym :
         forall sym ys,
           nullable_prod sym ys
           -> nullable_sym sym.

Scheme nullable_prod_mutual_ind := Induction for nullable_prod Sort Prop
  with nullable_gamma_mutual_ind := Induction for nullable_gamma Sort Prop
  with nullable_sym_mutual_ind := Induction for nullable_sym Sort Prop.


Definition nullable_set_complete (nu : SymbolSet.t)
                                 (g  : grammar) : Prop :=
  forall x, (@nullable_sym g) (NT x) -> SymbolSet.In (NT x) nu.

Definition nullable_set_minimal (nu : SymbolSet.t)
                                (g  : grammar) : Prop :=
  forall x, SymbolSet.In (NT x) nu -> (@nullable_sym g) (NT x).

Definition nullable_set_for nu g : Prop :=
nullable_set_complete nu g /\ nullable_set_minimal nu g.

Inductive first_prod {g : grammar} :
    lookahead -> symbol -> list symbol -> Prop :=
| FiProd : forall la x gamma,
    In (x, gamma) g.(productions)
    -> first_gamma la gamma
    -> first_prod la (NT x) gamma
with first_gamma {g : grammar} :
       lookahead -> list symbol -> Prop :=
     | FiGammaHd : forall la hd tl,
         first_sym la hd
         -> first_gamma la (hd :: tl)
     | FiGammaTl : forall la x tl,
         (@nullable_sym g) (NT x)
         -> first_gamma la tl
         -> first_gamma la (NT x :: tl)
with first_sym {g : grammar} :
       lookahead -> symbol -> Prop :=
| FiT : forall s,
    first_sym (LA s) (T s)
| FiNT : forall la sym gamma,
    first_prod la sym gamma
    -> first_sym la sym.

Scheme first_prod_mutual_ind := Induction for first_prod Sort Prop
  with first_gamma_mutual_ind := Induction for first_gamma Sort Prop
  with first_sym_mutual_ind := Induction for first_sym Sort Prop.

Definition first_set_complete fi g : Prop :=
  forall x la,
    isNT x = true
    -> (@first_sym g) la x
    -> exists xFirst,
        SymbolMap.find x fi = Some xFirst
        /\ LookaheadSet.In la xFirst.

Definition first_set_minimal fi g : Prop :=
  forall x xFirst la,
    SymbolMap.find x fi = Some xFirst
    -> LookaheadSet.In la xFirst
    -> (@first_sym g) la x.

Definition first_set_for fi g : Prop :=
first_set_complete fi g /\ first_set_minimal fi g.

Inductive follow_prod {g : grammar} :
  lookahead -> symbol -> list symbol -> Prop :=
| FoProd :
    forall la x gamma,
      In (x, gamma) g.(productions)
      -> follow_sym la (NT x)
      -> follow_prod la (NT x) gamma
with follow_sym {g : grammar} :
       lookahead -> symbol -> Prop :=
     | FoNu :
         forall sym gamma,
           (@nullable_prod g) sym gamma
           -> follow_sym EOF sym
     | FoRight :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@first_gamma g) la suffix
           -> follow_sym la (NT x2)
     | FoLeft :
         forall x1 x2 prefix suffix la,
           In (x1, prefix ++ NT x2 :: suffix) g.(productions)
           -> (@nullable_gamma g) suffix
           -> follow_sym la (NT x1)
           -> follow_sym la (NT x2).

Scheme follow_prod_mutual_ind := Induction for follow_prod Sort Prop
  with follow_sym_mutual_ind := Induction for follow_sym Sort Prop.

Definition follow_set_complete fo g : Prop :=
  forall x y,
    (@follow_sym g) y x
    -> exists xFollow,
      SymbolMap.find x fo = Some xFollow
      /\ LookaheadSet.In y xFollow.

Definition follow_set_minimal fo g : Prop :=
  forall x xFollow y,
    SymbolMap.find x fo = Some xFollow
    -> LookaheadSet.In y xFollow
    -> (@follow_sym g) y x.

Definition follow_set_for fo g : Prop :=
follow_set_complete fo g /\ follow_set_minimal fo g.

Definition lookahead_for {g} la sym gamma :=
  (@first_prod g) la sym gamma
  \/ ((@nullable_prod g) sym gamma
      /\ (@follow_prod g) la sym gamma).

Definition pt_minimal tbl g :=
  forall x la gamma laMap,
    StringMap.find x tbl = Some laMap
    -> LookaheadMap.find la laMap = Some gamma
    -> (@lookahead_for g) la (NT x) gamma.

Definition pt_complete tbl g :=
  forall x la gamma,
    (@lookahead_for g) la (NT x) gamma
    -> exists laMap,
      StringMap.find x tbl = Some laMap
      /\ LookaheadMap.find la laMap = Some gamma.

Definition parse_table_for (tbl : parse_table) (g : grammar) :=
  pt_minimal tbl g /\ pt_complete tbl g.
