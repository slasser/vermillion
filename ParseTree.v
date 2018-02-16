Require Import Grammar.
Require Import String.
(* Type variable seems to be cluttering up the definitions below. *)

Section ParseTree.

Variable A : Type.

Inductive tree :=
| Leaf : string -> tree
| Node : string -> forest -> tree
with forest :=
     | Fnil : forest
     | Fcons : tree -> forest -> forest.

Definition isNode (tr : tree) : bool :=
  match tr with
  | Node _ _ => true
  | Leaf _   => false
  end.

Definition isLeaf (tr : tree) : bool :=
  negb (isNode tr).

Scheme tree_mutual_ind := Induction for tree Sort Prop
  with forest_mutual_ind := Induction for forest Sort Prop.

End ParseTree.