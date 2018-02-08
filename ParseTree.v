Require Import Grammar.

(* Type variable seems to be cluttering up the definitions below. *)
Inductive parse_tree {A} :=
| Leaf : A -> parse_tree
| Node : A -> list parse_tree -> parse_tree.

Definition getRoot (tree : parse_tree) : symbol :=
  match tree with
  | Node ntName _ => NT ntName
  | Leaf tName    => T tName
  end.

Definition isNode {A} (tree : (@parse_tree A)) : bool :=
  match tree with
  | Node _ _ => true
  | Leaf _   => false
  end.

Definition isLeaf {A} (tree : (@parse_tree A)) : bool :=
  negb (isNode tree).