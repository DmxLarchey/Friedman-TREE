```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```
# Friedman-TREE

In this small project, depending on [`Coq-Kruskal`](https://github.com/DmxLarchey/Coq-Kruskal) in an essential way,
we build [Harvey Friedman](https://en.wikipedia.org/wiki/Harvey_Friedman)'s `tree(n)` and `TREE(n)` fast growing functions.

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
as the largest natural number `m` for which there is a sequence of length `m` of undecorated
rose trees `[t₁;...;tₘ]` such that:
1. the number of nodes of those trees are `1+n,...,m+n` respectivelly; 
2. the sequence is bad for the homeomorphic embedding `≤ₕ`.

Formally in Coq, this gives the following specification and the theorem `Friedman_tree_spec` established in [`tree.v`](theories/tree.v):
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
   ↔ ∃ t : vec rtree m, (∀i, ⌊tᵢ⌋ᵣ = 1+i+n) ∧ (∀ i j, i < j → ¬ tᵢ ≤ₕ tⱼ).
```

The essential argument to built the value `Friedman_tree n` is to show that there is a length `m` such that any sequence
of trees `[t₁;...;tₘ]` of increasing sizes (as specified above) is good for the homeomorphic embedding `≤ₕ`:
- first, using Kruskal's theorem in its (equivalent) formulation using inductive bars, any (ever expending)
  sequence of trees is bound to become `≤ₕ`-good;
- second, at any given value `s`, the trees which have size `s` are finitely many;
- hence, we build the "set" of size increasing sequences of trees as a _finitary FAN_, ie a
  finite collection of choice sequences;
- then, applying the FAN theorem for inductive bars, all the size increasing sequences are bound to
  become `≤ₕ`-good _uniformly_, ie all simultaneously;
- the point `m` where all the size increasing sequences of length `m` become `≤ₕ`-good is the needed value.
 
Since, the spec of `Friedman_tree n` is decidable, anti-monotonic and bounded (by the above `m`), 
the value `Friedman_tree n` can be computed by linear search using a variant of Constructive Epsilon.

Notice that our implementation is _axiom free_, hence purely constructive. Compared to the argument developed in [Wikipedia](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem), we here use a _constructive version of Kruskal's theorem_ from [`Kruskal-Theorems`](https://github.com/DmxLarchey/Kruskal-Theorems), and we replace _Koenig's lemma_ with the FAN theorem for inductive bars as established constructivelly also in [`Kruskal-Higman`](https://github.com/DmxLarchey/Kruskal-Higman).

## The Friedman `TREE(n)` function

The Friedman `TREE(n)` function is [insanely fast growing function](https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem) of which the termination proof depends on the proof of Kruskal's tree theorem itself. The construction we perfom in Coq is similar to the previous one but operates on rose trees decorated with the finite type `idx n ≃ [1,...,n]` where `n` is the parameter of `Friedman_TREE n`. The construction of `Friedman_TREE` and the theorem `Friedman_TREE_spec` are performed in [`TREE.v`](theories/TREE.v):

```coq
Definition ntree (n : nat) := ltree (idx n).
Notation "⟨i|l⟩ₗ" := (ltree_node i l).

Definition ntree_size {n} : ntree n → nat := @ltree_size _.
Notation "⌊ t ⌋ₙ" := (ntree_size t).
Fact ntree_size_fix i l : ⌊⟨i,l⟩ₗ⌋ₙ = 1 + list_sum ntree_size l.

Definition ntree_embed {n} : rel₂ (ntree n) := ltree_homeo_embed (@eq _).
Notation "l ≤ₕ m" := (ntree_homeo_embed l m).

Definition Friedman_TREE : nat → nat.

Theorem Friedman_TREE_spec n :
 ∀m, m ≤ Friedman_TREE n
   ↔ ∃ t : vec (ntree n) m, (∀i, ⌊tᵢ⌋ₙ ≤ 1+i) ∧ (∀ i j, i < j → ¬ tᵢ ≤ₕ tⱼ).
```
