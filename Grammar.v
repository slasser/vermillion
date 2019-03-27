Require Import List PeanoNat String.
Require Import FMaps MSets.
Export ListNotations.

(* Types of grammar symbols and their decidable equality *)
Module Type SYMBOL_TYPES.
  Parameters terminal nonterminal literal : Type.
  
  Hypothesis t_eq_dec : forall a a' : terminal,
      {a = a'} + {a <> a'}.
  
  Hypothesis nt_eq_dec : forall x x' : nonterminal,
      {x = x'} + {x <> x'}.
End SYMBOL_TYPES.

(* Functor that builds symbol definitions for the given symbol types *)
Module SymbolFn (Import SymTy : SYMBOL_TYPES).
  
  Inductive symbol :=
  | T  : terminal -> symbol
  | NT : nonterminal -> symbol.

  Hint Resolve SymTy.t_eq_dec SymTy.nt_eq_dec.
  
  Lemma symbol_eq_dec : forall s s' : symbol,
      {s = s'} + {s <> s'}.
  Proof. decide equality. Defined.

  Definition production := (nonterminal * list symbol)%type.

  Definition token := (terminal * literal)%type.

End SymbolFn.

Module Type SYMBOL (SymTy : SYMBOL_TYPES).
  Include SymbolFn SymTy.
End SYMBOL.

(* Grammar representation that the user should provide to the tool. *)
Module Type INIT.
  Declare Module SymTy : SYMBOL_TYPES.
  Declare Module Sym   : SYMBOL SymTy.
  Export SymTy.
  Export Sym.
  Parameter startSymbol : nonterminal.
  Parameter productions : list Sym.production.
End INIT.

(* Accompanying definitions for a grammar. *)
Module DefsFn (Export Init : INIT).

  (* We represent a grammar as a record so that functions 
     can consume the start symbol and productions easily. *)
  Record grammar := {start : nonterminal ;
                     prods : list production }.
    
  (* Derivation trees *)
  Module Export Tree.
    
    Inductive tree :=
    | Leaf : terminal -> tree
    | Node : nonterminal -> list tree -> tree.
    
    Definition isNode (tr : tree) : bool :=
      match tr with
      | Node _ _ => true
      | Leaf _   => false
      end.
    
    Definition isLeaf (tr : tree) : bool :=
      negb (isNode tr).
  
    (* Induction principles for trees and lists of trees *)
    Section tree_nested_ind.
      Variable P : tree -> Prop.
      Variable Q : list tree -> Prop.
      Hypothesis Hleaf : forall y, P (Leaf y).
      Hypothesis Hnode : forall x l, Q l -> P (Node x l).
      Hypothesis Hnil  : Q nil.
      Hypothesis Hcons : forall t, P t -> forall l, Q l -> Q (t :: l).
      
      Fixpoint tree_nested_ind t : P t :=
        match t with
        | Leaf y => Hleaf y
        | Node x l =>
          Hnode x l
                (((fix l_ind l' : Q l' :=
                     match l' with
                     | nil => Hnil
                     | hd :: tl => Hcons hd (tree_nested_ind hd) tl (l_ind tl)
                     end)) l)
        end.
      
      Fixpoint forest_nested_ind l : Q l :=
        match l with
        | nil => Hnil
        | hd :: tl => Hcons hd (tree_nested_ind hd) tl (forest_nested_ind tl)
        end.
    End tree_nested_ind.
  End Tree.

  (* NULLABLE, FIRST, FOLLOW, and LOOKAHEAD relational definitions *)
  Module Export Lookahead.
    Open Scope list_scope.
    
    Inductive lookahead :=
    | LA  : terminal -> lookahead
    | EOF : lookahead.

    Inductive nullable_sym (g : grammar) : symbol -> Prop :=
    | NullableSym : forall (x : nonterminal) (ys : list symbol),
        In (x, ys) g.(prods)
        -> nullable_gamma g ys
        -> nullable_sym g (NT x)
    with nullable_gamma (g : grammar) : list symbol -> Prop :=
         | NullableNil  : nullable_gamma g []
         | NullableCons : forall (hd : symbol) (tl : list symbol),
             nullable_sym g hd
             -> nullable_gamma g tl
             -> nullable_gamma g (hd :: tl).
    
    Hint Constructors nullable_sym nullable_gamma.
    
    Scheme nullable_sym_mutual_ind := Induction for nullable_sym Sort Prop
      with nullable_gamma_mutual_ind := Induction for nullable_gamma Sort Prop.

    Inductive first_sym (g : grammar) :
      lookahead -> symbol -> Prop :=
    | FirstT : forall y,
        first_sym g (LA y) (T y)
    | FirstNT : forall x gpre s gsuf la,
        In (x, gpre ++ s :: gsuf) g.(prods)
        -> nullable_gamma g gpre
        -> first_sym g la s
        -> first_sym g la (NT x).
    
    Hint Constructors first_sym.

    Inductive first_gamma (g : grammar) : lookahead -> list symbol -> Prop :=
    | FirstGamma : forall gpre la s gsuf,
        nullable_gamma g gpre
        -> first_sym g la s
        -> first_gamma g la (gpre ++ s :: gsuf).
    
    Hint Constructors first_gamma.

    Inductive follow_sym (g : grammar) : lookahead -> symbol -> Prop :=
    | FollowStart : forall x,
        x = g.(start)
        -> follow_sym g EOF (NT x)
    | FollowRight : forall x1 x2 la gpre gsuf,
        In (x1, gpre ++ NT x2 :: gsuf) g.(prods)
        -> first_gamma g la gsuf
        -> follow_sym g la (NT x2)
    | FollowLeft : forall x1 x2 la gpre gsuf,
        In (x1, gpre ++ NT x2 :: gsuf) g.(prods)
        -> nullable_gamma g gsuf
        -> follow_sym g la (NT x1)
        -> follow_sym g la (NT x2).

    Hint Constructors follow_sym.

    (* "la is a lookahead token for production X -> gamma" *)
    Definition lookahead_for
               (la : lookahead)
               (x : nonterminal)
               (gamma : list symbol)
               (g : grammar) : Prop :=
      first_gamma g la gamma
      \/ (nullable_gamma g gamma
          /\ follow_sym g la (NT x)).
    
  End Lookahead.

  (* Finite sets, maps, and tables *)
  Module Export Collections.

    Module MDT_NT.
      Definition t := nonterminal.
      Definition eq_dec := Init.SymTy.nt_eq_dec.
    End MDT_NT.
    Module NT_as_DT := Make_UDT(MDT_NT).
    Module NtSet := MSetWeakList.Make NT_as_DT.
    Module NtMap := FMapWeakList.Make NT_as_DT.
    
    Definition lookahead_eq_dec :
      forall (lk lk2 : lookahead),
        {lk = lk2} + {~lk = lk2}.
    Proof. decide equality. Defined.
    
    Module MDT_Lookahead.
      Definition t := lookahead.
      Definition eq_dec := lookahead_eq_dec.
    End MDT_Lookahead.
    Module Lookahead_as_DT := Make_UDT(MDT_Lookahead).
    Module LaSet := MSetWeakList.Make Lookahead_as_DT.

    Definition pt_key := (nonterminal * lookahead)%type.
    
    Definition pt_key_eq_dec :
      forall k k2 : pt_key,
        {k = k2} + {k <> k2}.
    Proof. repeat decide equality. Defined.
    
    Module MDT_PtKey.
      Definition t := pt_key.
      Definition eq_dec := pt_key_eq_dec.
    End MDT_PtKey.
    
    Module PtKey_as_DT := Make_UDT(MDT_PtKey).
    
    Module ParseTable := FMapWeakList.Make PtKey_as_DT.
    
    Definition first_map := NtMap.t LaSet.t.
    Definition follow_map := NtMap.t LaSet.t.
    Definition parse_table := ParseTable.t (list symbol).
    
  End Collections.

  (* Lemmas about finite collections *)  
  Module Export CollectionFacts.
    Module Export NtSetFacts := WFactsOn NT_as_DT NtSet.
    Module Export NtSetEqProps := EqProperties NtSet.
    Module Export NtMapFacts := WFacts_fun NT_as_DT NtMap.
    
    Module Export LaSetFacts := WFactsOn Lookahead_as_DT LaSet.
    Module Export LaSetEqProps := EqProperties LaSet.

    Module Export ParseTableFacts := WFacts_fun PtKey_as_DT ParseTable.
    
    Module Export NP := MSetProperties.Properties NtSet.
    Module Export ND := WDecideOn NT_as_DT NtSet.
    
    Module Export LP := MSetProperties.Properties LaSet.
    Module Export LD := WDecideOn Lookahead_as_DT LaSet.
  End CollectionFacts.

    (* Grammar semantics *)
  Module Export Derivation.

    Definition peek input :=
      match input with
      | nil => EOF
      | token :: _ => LA token
      end.

    Inductive sym_derives_prefix {g : grammar} :
      symbol -> list terminal -> tree -> list terminal -> Prop :=
    | T_sdp : 
        forall (y : terminal) (rem : list terminal),
          sym_derives_prefix (T y) [y] (Leaf y) rem
    | NT_sdp :
        forall (x : nonterminal) 
               (gamma : list symbol)
               (word rem : list terminal) 
               (subtrees : list tree),
          In (x, gamma) g.(prods)
          -> lookahead_for (peek (word ++ rem)) x gamma g
          -> gamma_derives_prefix gamma word subtrees rem
          -> sym_derives_prefix (NT x) word (Node x subtrees) rem
    with gamma_derives_prefix {g : grammar} : 
           list symbol -> list terminal -> list tree -> list terminal -> Prop :=
         | Nil_gdp : forall rem,
             gamma_derives_prefix [] [] [] rem
         | Cons_gdp : 
             forall (hdRoot : symbol)
                    (wpre wsuf rem : list terminal)
                    (hdTree : tree)
                    (tlRoots : list symbol)
                    (tlTrees : list tree),
               sym_derives_prefix hdRoot wpre hdTree (wsuf ++ rem)
               -> gamma_derives_prefix tlRoots wsuf tlTrees rem
               -> gamma_derives_prefix (hdRoot :: tlRoots) 
                                       (wpre ++ wsuf)
                                       (hdTree :: tlTrees)
                                       rem.
    
    Hint Constructors sym_derives_prefix gamma_derives_prefix.
    
    Scheme sdp_mutual_ind := Induction for sym_derives_prefix Sort Prop
      with gdp_mutual_ind := Induction for gamma_derives_prefix Sort Prop.

  End Derivation.

  Module Export Utils.
    
    Definition pt_lookup
               (x   : nonterminal)
               (la  : lookahead)
               (tbl : parse_table) : option (list symbol) :=
      ParseTable.find (x, la) tbl.
    
    Definition pt_add
               (x : nonterminal)
               (la : lookahead)
               (gamma : list symbol)
               (tbl : parse_table) : parse_table :=
      ParseTable.add (x, la) gamma tbl.

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
      
      Definition fromNtList (ls : list nonterminal) : NtSet.t :=
        fold_right NtSet.add NtSet.empty ls.
      
  End Utils.

  (* Definitions related to orrectness specs *)
  Module Export Specs.

    Definition nullable_set_sound (nu : NtSet.t) (g  : grammar) : Prop :=
      forall (x : nonterminal), NtSet.In x nu -> nullable_sym g (NT x).
    
    Definition nullable_set_complete (nu : NtSet.t) (g  : grammar) : Prop :=
      forall (x : nonterminal), nullable_sym g (NT x) -> NtSet.In x nu.
    
    Definition nullable_set_for (nu : NtSet.t) (g : grammar) : Prop :=
      nullable_set_sound nu g /\ nullable_set_complete nu g.

    Definition first_map := NtMap.t LaSet.t.
    
    Definition first_map_sound (fi : first_map) (g : grammar) : Prop :=
      forall x xFirst la,
        NtMap.find x fi = Some xFirst
        -> LaSet.In la xFirst
        -> first_sym g la (NT x).
    
    (* We want a symbol in the first_sym hypothesis
       instead of an (NT x) so that induction is stronger *)
    Definition first_map_complete (fi : first_map) (g : grammar) : Prop :=
      forall la sym x,
        first_sym g la sym
        -> sym = NT x
        -> exists xFirst,
            NtMap.find x fi = Some xFirst
            /\ LaSet.In la xFirst.
    
    Definition first_map_for (fi : first_map) (g : grammar) : Prop :=
      first_map_sound fi g /\ first_map_complete fi g.

    Definition follow_map := NtMap.t LaSet.t.
    
    Definition follow_map_sound (fo : follow_map) (g : grammar) : Prop :=
      forall x xFollow la,
        NtMap.find x fo = Some xFollow
        -> LaSet.In la xFollow
        -> follow_sym g la (NT x).
    
    Definition follow_map_complete (fo : follow_map) (g : grammar) : Prop :=
      forall s x la,
        follow_sym g la s
        -> s = NT x
        -> exists xFollow,
            NtMap.find x fo = Some xFollow
            /\ LaSet.In la xFollow.
    
    Definition follow_map_for (fo : follow_map) (g : grammar) : Prop :=
      follow_map_sound fo g /\ follow_map_complete fo g.
    
    Definition pt_sound (tbl : parse_table) (g : grammar) :=
      forall (x : nonterminal) (la : lookahead) (gamma : list symbol),
        pt_lookup x la tbl = Some gamma
        -> List.In (x, gamma) g.(prods) /\ lookahead_for la x gamma g.
    
    Definition pt_complete (tbl : parse_table) (g : grammar) :=
      forall (x : nonterminal) (la : lookahead) (gamma : list symbol),
        List.In (x, gamma) g.(prods)
        -> lookahead_for la x gamma g
        -> pt_lookup x la tbl = Some gamma.
    
    Definition parse_table_correct (tbl : parse_table) (g : grammar) :=
      pt_sound tbl g /\ pt_complete tbl g.

  End Specs.

End DefsFn.

Module Type DefsT (Init : INIT).
  Include DefsFn Init.
End DefsT.

Module Type T.
  Declare Module Init : INIT.
  Declare Module Defs : DefsT Init.
  Export Init.
  Export Defs.
End T.

(* Simple example of how to build a concrete grammar. *)
(* First, we provide the symbol types, start symbol, and productions *)
Open Scope string_scope.
Module I : INIT.
  Module SymTy.
    Definition terminal := string.
    Definition nonterminal := nat.
    Definition literal := string.
    Definition t_eq_dec := string_dec.
    Definition nt_eq_dec := Nat.eq_dec.
  End SymTy.
  Module Sym := SymbolFn SymTy.
  Export SymTy.
  Export Sym.
  Definition startSymbol := 0.
  Definition productions := [(0, [T "hello"; NT 0])].
End I.

(* Next, we generate the accompanying definitions for the grammar *)
Module D : DefsT I := DefsFn I.

(* Now we can package the initial portion and related definitions. *)
Module G : T.
  Module Init := I.
  Module Defs := D.
  Export Init.
  Export Defs.
End G.

