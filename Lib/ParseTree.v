Require Import String List.
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

Section more_ind.

  Variable P : tree -> Prop.
  Variable Q : forest -> Prop.

  Hypothesis H : forall s l, Q l -> P (Node s l).
  Hypothesis H0 : Q Fnil.
  Hypothesis H1 :
    forall tr,
      P tr
      -> forall l,
        Q l
        -> Q (Fcons tr l).
  Hypothesis H2 : forall y, P (Leaf y).

  Import ListNotations.

  Fixpoint tree_nested_ind t : P t :=
    match t with
    | Leaf y => H2 y
    | Node x l =>
      H x l
        (((fix l_ind l' : Q l' :=
             match l' with
             | Fnil => H0
             | Fcons t1 tl => H1 t1 (tree_nested_ind t1) tl (l_ind tl)
             end)) l)
    end.
End more_ind.

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

Fixpoint All (f : forest) (P : tree -> Prop) : Prop :=
  match f with
  | Fnil => True
  | Fcons tr f' => P tr /\ All f' P
  end.

Section tree2.

  Inductive ptree :=
  | PLeaf : string -> ptree
  | PNode : string -> list ptree -> ptree.

  Variable P : ptree -> Prop.
  Variable Q : list ptree -> Prop.

  Hypothesis H : forall s l, Q l -> P (PNode s l).
  Hypothesis H0 : Q nil.
  Hypothesis H1 :
    forall tr,
      P tr
      -> forall l,
        Q l
        -> Q (tr :: l).
  Hypothesis H2 : forall y, P (PLeaf y).

  Import ListNotations.

  Fixpoint ptree_ind' t : P t :=
    match t with
    | PLeaf y => H2 y
    | PNode x l =>
      H x l
        (((fix l_ind l' : Q l' :=
             match l' with
             | nil => H0
             | t1 :: tl => H1 t1 (ptree_ind' t1) tl (l_ind tl)
             end)) l)
    end.
End tree2.

