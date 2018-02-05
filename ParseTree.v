Require Import Grammar.

Inductive parse_tree {A} :=
| Leaf : A -> parse_tree
| Node : A -> list parse_tree -> parse_tree.


Definition getRoot (tree : parse_tree) : symbol :=
  match tree with
  | Node ntName _ => NT ntName
  | Leaf tName    => T tName
  end.