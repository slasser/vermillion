Require Import List.
Require Import Grammar.

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

