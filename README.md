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

The Friedman `tree(n)` function is [informally defined](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem)
as the largest natural number `m` for which there is a sequence `[t₁;...;tₘ]` of length `m` of undecorated
rose trees such that:
1. the number of nodes of those trees are `1+n,...,m+n` respectivelly; 
2. the sequence is bad for the homeomorphic embedding.

Formally in Coq, this gives the following specification:
```coq

Inductive rtree : Type :=  ⟨ _ ⟩ᵣ : list rtree → rtree.

Inductive rtree_homeo_embed : rtree → rtree → Prop :=
  | rtree_homeo_embed_subt s t l : t ∈ l → s ≤ₕ t → s ≤ₕ ⟨l⟩ᵣ
  | rtree_homeo_embed_root l m : list_embed rtree_homeo_embed l m → ⟨l⟩ᵣ ≤ₕ ⟨m⟩ᵣ
where "s ≤ₕ t" := (rtree_homeo_embed s t).

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

## The Friedman `TREE(n)` function
