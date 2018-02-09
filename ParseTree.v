Require Import Grammar.
Require Import String.
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

(* New stuff is here *)

Inductive tree :=
| Lf : string -> tree
| Nd : string -> forest -> tree
with forest :=
     | Fnil : forest
     | Fcons : tree -> forest -> forest.

Fixpoint appForest xs ys :=
  match xs with
  | Fnil => ys
  | Fcons t xs' => Fcons t (appForest xs' ys)
  end.
  

Fixpoint revForest ts :=
  match ts with
  | Fnil => Fnil
  | Fcons t ts' => appForest (revForest ts') (Fcons t Fnil)
  end.

Scheme tree_ind' := Induction for tree Sort Prop
  with forest_ind' := Induction for forest Sort Prop.

Require Import List.
Import ListNotations.

Inductive derTree {g : grammar} : symbol -> list string -> tree -> Prop :=
| derT : forall (y : string),
    derTree (T y) [y] (Lf y)
| derNT : forall (x : string) (gamma : list symbol) (tokens : list string) (subtrees : forest),
    In (NT x, gamma) g ->
    derForest gamma tokens subtrees ->
    derTree (NT x) tokens (Nd x subtrees)
with derForest {g : grammar} : list symbol -> list string -> forest -> Prop :=
     | derFnil : derForest [] [] Fnil
     | derFcons : forall (hdRoot : symbol)
                         (prefix : list string)
                         (hdSubtree : tree)
                         (tlRoots : list symbol)
                         (suffix : list string)
                         (tlSubtrees : forest),
         derTree hdRoot prefix hdSubtree ->
         derForest tlRoots suffix tlSubtrees ->
         derForest (hdRoot :: tlRoots) (prefix ++ suffix) (Fcons hdSubtree tlSubtrees).