(* A generic result constructing permutation trees. *)

From stdpp Require Import list.

Section Generic.

Variable X : Type.
Context `{Equiv X}.

Inductive tree :=
  | Leaf
  | Node (x : X) (l r : tree).

Fixpoint flatten t :=
  match t with
  | Leaf => []
  | Node x l r => x :: flatten l ++ flatten r
  end.

Fixpoint grow t x :=
  match t with
  | Leaf => [Node x Leaf Leaf]
  | Node y l r =>
    ((λ l, Node y l r) <$> grow l x) ++
    ((λ r, Node y l r) <$> grow r x)
  end.

Definition tree_permutations l :=
  foldl (λ ts x, flat_map (λ t, grow t x) ts) [Leaf] l.

Theorem tree_permutations_spec l l' :
  l' ∈ flatten <$> tree_permutations l <-> l' ∈ permutations l.
Proof.
Admitted.

End Generic.
