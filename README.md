# Friedman-TREE

## Reminders:

```coq

Fixpoint list_sum {X} (f : X → nat) l :=
  match l with
  | [] => 0
  | x :: l => f x + list_sum l
  end.

(** Reminder:
    idx m ≃ {0,...,m-1}.
    vec X m are vectors of carrier type X and length m
    If v : vec X m and i : idx m, then vᵢ is the i-th component of v *)

Inductive idx : nat → Type.
Inductive vec : Type → nat → Type.
```

## The Friedman `tree(n)` function

```coq

Inductive rtree : Type :=  ⟨ _ ⟩ᵣ : list rtree → rtree.

Definition rtree_size : rtree → nat.
Notation "⌊ t ⌋ᵣ" := (rtree_size t).

Fact rtree_size_fix l : ⌊⟨l⟩ᵣ⌋ᵣ = 1 + list_sum rtree_size l.

Definition Friedman_tree : nat → nat.

Theorem Friedman_tree_spec n :
 ∀m, m ≤ Friedman_tree n
   ↔ ∃ t : vec rtree m,
        (∀ i : idx m, ⌊tᵢ⌋ᵣ = 1+i+n)
       ∧ ∀ i j : idx m, i < j → ¬ tᵢ ≤ₕ tⱼ.
```
