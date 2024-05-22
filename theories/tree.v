(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith Lia Utf8.

From KruskalTrees
  Require Import notations tactics list_utils idx vec rtree.

From KruskalFinite
  Require Import finite decide examples.trees. (* examples is for finiteness wrt weight *)

From KruskalAfProp
  Require Import base notations almost_full.

From KruskalFanProp
  Require Import af_konig.

Require Import epsilon_max rtree_embed.

Import ListNotations idx_notations vec_notations rtree_notations.

Set Implicit Arguments.

#[local] Notation "l ≤ₕ m" := (rtree_homeo_embed l m) (at level 70, no associativity, format "l  ≤ₕ  m").
#[local] Notation FAN lc := (λ c, Forall2 (λ x l, x ∈ l) c lc).

Section Friedman_tree.

  Variable (n : nat).

  (** This is the characterization of tree(n) as
      described on eg Wikipedia, i.e.
      the *largest* m such that tree_n_spec m

      See https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem

      tree_n_spec m says that
      there is a sequence [t₁;...;tₘ] of rtree
       * where tᵢ has i+n vertices for any i ∈ [1,m]
       * tᵢ ≤ₕ tⱼ holds for no i < j ∈ [1,m]

      Notice that with vectors, idx2nat start from 0, not 1 *)

  Let tree_n_size m (t : vec rtree m) := ∀i, ⌊t⦃i⦄⌋ᵣ = (1+idx2nat i)+n.
  Let tree_n_bad m (t : vec rtree m) := ∀ i j, idx2nat i < idx2nat j → ¬ t⦃i⦄ ≤ₕ t⦃j⦄.

  Let tree_n_spec m := ∃t : vec rtree m, tree_n_size t ∧ tree_n_bad t.

  (** We apply a constructive form of König's lemma for an AF relation.
      For a given finitary FAN, there is a length m such that every
      choice sequence over this FAN contains a good pair *)

  Local Theorem tree_n_size_good : ∃ₜ m, ∀t : vec rtree m, tree_n_size t → ∃ i j, idx2nat i < idx2nat j ∧ t⦃i⦄ ≤ₕ t⦃j⦄.
    Proof.
      apply af_konig with (P := fun k t => ⌊t⌋ᵣ = 1+k+n).
      + apply af_rtree_homeo_embed.
      + intro; apply fin_rtree_size_eq.
    Qed.

   (* The above m does not satisfy tree_n_spec m *)

  Local Corollary tree_n_spec_fails : ∃ₜ m, ¬ tree_n_spec m.
  Proof.
    destruct tree_n_size_good as (m & Hm).
    exists m; intros (v & H1 & H2).
    apply Hm in H1 as (p & q & H3 & H4).
    apply (H2 p q); auto.
  Qed.

  Hint Resolve lt_dec
               rtree_homeo_embed_dec
               fin_rtree_size_eq
               tree_n_spec_fails : core.

  (** We build the value of (Friedman) tree(n) packed
      with its specification using a tailored version
      of Constructive Epsilon. *)

  Local Lemma tree_n_pwc : { Ft | ∀m, m ≤ Ft ↔ tree_n_spec m }.
  Proof.
    apply epsilon_maximal; eauto.
    + intros i; unfold tree_n_spec.
      decide auto.
      * apply fin_idx_rel with (R := fun p (t : rtree) => ⌊t⌋ᵣ = 1 + idx2nat p+n); eauto.
      * intros ? _; decide auto; fin auto.
        intro; apply decider_forall_finite; fin auto.
        intro; decide auto.
    + exists vec_nil; split; intros p; idx invert p; auto.
    + intros i j Hij (v & H1 & H2).
      exists (vec_set (fun p => vec_prj v (idx_emb Hij p))); split.
      * intro; rewrite vec_prj_set, (idx2nat_emb Hij); auto.
      * intros p q Hpq; rewrite !vec_prj_set.
        apply H2; rewrite <- !idx2nat_emb; auto.
  Qed.

  (* We project tree_n_pwc to get (Friedman) tree(n) *)

  Definition Friedman_tree := proj1_sig tree_n_pwc.

  Theorem Friedman_tree_spec m : m ≤ Friedman_tree ↔ tree_n_spec m.
  Proof. apply (proj2_sig tree_n_pwc). Qed.

End Friedman_tree.

Print rtree.
Check rtree_size_fix.
Print list_sum.

Check Friedman_tree.
Check Friedman_tree_spec.
Print Assumptions Friedman_tree_spec.


