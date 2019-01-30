Require Import List.
Require Import Grammar ParseTree ParseTable
        Lib.Tactics.
Import ListNotations.
Open Scope list_scope.

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
      In (x, gamma) g.(productions)
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

Scheme sdp_mutual_ind := Induction for sym_derives_prefix Sort Prop
  with gdp_mutual_ind := Induction for gamma_derives_prefix Sort Prop.

