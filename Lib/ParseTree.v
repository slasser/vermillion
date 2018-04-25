Require Import String.
Require Import Grammar.

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

Combined Scheme tree_forest_mutual_ind
         from tree_mutual_ind, forest_mutual_ind.

Fixpoint span tr :=
  match tr with
  | Leaf _ => 1
  | Node _ sts =>
    spanForest sts
  end
with spanForest f :=
       match f with
       | Fnil => 0
       | Fcons hd tl =>
         span hd + spanForest tl
       end.
