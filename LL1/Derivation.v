Require Import List String.
Require Import Grammar LL1.Parser ParseTree ParseTable
        Lib.Tactics.
Import ListNotations.
Open Scope list_scope.

Inductive sym_derives_prefix {g : grammar} :
  symbol -> list string -> tree -> list string -> Prop :=
| T_sdp : 
    forall (y : string) (rem : list string),
      sym_derives_prefix (T y) [y] (Leaf y) rem
| NT_sdp :
    forall (x : string) 
           (gamma : list symbol)
           (word rem : list string) 
           (subtrees : list tree),
      (@lookahead_for g) (peek (word ++ rem)) (NT x) gamma
      -> gamma_derives_prefix gamma word subtrees rem
      -> sym_derives_prefix (NT x) word (Node x subtrees) rem
with gamma_derives_prefix {g : grammar} : 
       list symbol -> list string -> list tree -> list string -> Prop :=
     | Nil_gdp : forall rem,
         gamma_derives_prefix [] [] [] rem
     | Cons_gdp : 
         forall (hdRoot : symbol)
                (wpre wsuf rem : list string)
                (hdTree : tree)
                (tlRoots : list symbol)
                (tlTrees : list tree),
         sym_derives_prefix hdRoot wpre hdTree (wsuf ++ rem)
         -> gamma_derives_prefix tlRoots wsuf tlTrees rem
         -> gamma_derives_prefix (hdRoot :: tlRoots) 
                                 (wpre ++ wsuf)
                                 (hdTree :: tlTrees)
                                 rem.

Scheme sdp_mutual_ind := Induction for sym_derives_prefix Sort Prop
  with gdp_mutual_ind := Induction for gamma_derives_prefix Sort Prop.
