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
  Require Import notations tactics list_utils idx vec ltree ntree.

From KruskalFinite
  Require Import finite decide examples.trees. (* examples is for finiteness wrt weight *)

From KruskalAfProp
  Require Import base notations almost_full.

From KruskalHigmanProp
  Require Import tactics fan vec_embed.

Require Import epsilon_max pfx_utils ntree_embed.

Import ListNotations idx_notations vec_notations ltree_notations ntree_notations.

Set Implicit Arguments.

#[local] Notation "l ≤ₕ m" := (ntree_homeo_embed l m) (at level 70, no associativity, format "l  ≤ₕ  m").
#[local] Notation FAN lc := (λ c, Forall2 (λ x l, x ∈ l) c lc).

Section Friedman_TREE.

  Variable (n : nat).

  (** This is the characterization of TREE(n) as
      described on eg Wikipedia, i.e.
      the *largest* m such that TREE_n_spec m

      See https://en.wikipedia.org/wiki/Kruskal%27s_tree_theorem

      TREE_n_spec m says that
      there is a sequence [t₁;...;tₘ] of (ntree n)
       * where tᵢ has at most i vertices for any i ∈ [1,m]
       * tᵢ ≤ₕ tⱼ holds for no i < j ∈ [1,m]

      Notice that with vectors, idx2nat start from 0, not 1 *)

  Let TREE_n_size m (t : vec (ntree n) m) := ∀i, ⌊t⦃i⦄⌋ₙ ≤ 1+idx2nat i.
  Let TREE_n_bad m (t : vec (ntree n) m) := ∀ i j, idx2nat i < idx2nat j → ¬ t⦃i⦄ ≤ₕ t⦃j⦄.

  Let TREE_n_spec m := ∃t : vec (ntree n) m, TREE_n_size t ∧ TREE_n_bad t.

  Section TREE_n_spec_fails.

    (** We show the existence of a bound on m such that TREE_n_spec m *)

    Hint Resolve af_ntree_homeo_embed : core.

    (** We combine with the FAN theorem *)

    Local Lemma good_uniform_over_fans : bar (λ lc, FAN lc ⊆₁ good (@ntree_homeo_embed n)) [].
    Proof.
      apply FAN_theorem.
      + now constructor 2.
      + apply af_iff_bar_good; auto.
    Qed.

    (** We build TREE_n_size as a FAN, which will thus be good above some m *)

    (* trees k is the list of trees of size 1+k+n 
       Hence FAN (pfx_rev trees m) = FAN [trees (m-1);...;trees 0]
       collects all the possible reverse sequences st tree_cond *)
    Let trees k := proj1_sig (fin_ntree_size_le n (1+k)).

    Local Fact trees_spec k t : ⌊t⌋ₙ ≤ 1+k ↔ t ∈ trees k.
    Proof. apply (proj2_sig (fin_ntree_size_le _ _)). Qed.

    Local Fact TREE_n_size_iff_FAN m (t : vec _ m) :
       TREE_n_size t ↔ FAN (pfx_rev trees m) (rev (vec_list t)).
    Proof.
      rewrite <- Forall2_rev, rev_involutive,
              rev_pfx_rev_vec_list_eq, Forall2_iff_vec_fall2.
      apply forall_equiv; intros i.
      rewrite vec_prj_set, <- trees_spec; tauto.
    Qed.

    (** By the FAN theorem, FAN is uniformly good at some point *)

    Local Lemma FAN_is_good : ∃ₜ m, FAN (pfx_rev trees m) ⊆₁ good (@ntree_homeo_embed n).
    Proof. apply (bar_pfx_rev trees good_uniform_over_fans). Qed.

    (** Hence, at this same value m, any sequence satisfying tree_cond m is good *)

    Local Theorem TREE_n_size_good : ∃ₜ m, ∀t : vec (ntree n) m, TREE_n_size t → ∃ i j, idx2nat i < idx2nat j ∧ t⦃i⦄ ≤ₕ t⦃j⦄.
    Proof.
      destruct FAN_is_good as (m & Hm).
      exists m; intros v.
      rewrite TREE_n_size_iff_FAN.
      now intros H%Hm%good_rev_vec_list.
    Qed.

   (* The above m does not satisfy tree_n_spec m *)

    Local Corollary TREE_n_spec_fails : ∃m, ¬ TREE_n_spec m.
    Proof.
      destruct TREE_n_size_good as (m & Hm).
      exists m; intros (v & H1 & H2).
      apply Hm in H1 as (p & q & H3 & H4).
      apply (H2 p q); auto.
    Qed.

  End TREE_n_spec_fails.

  Hint Resolve lt_dec
               ntree_homeo_embed_dec
               fin_ntree_size_le
               TREE_n_spec_fails : core.

  (** We build the value of (Friedman) TREE(n) packed
      with its specification using a tailored version
      of Constructive Epsilon. *)

  Local Lemma TREE_n_pwc : { FT | ∀m, m ≤ FT ↔ TREE_n_spec m }.
  Proof.
    apply epsilon_maximal; eauto.
    + intros i; unfold TREE_n_spec.
      decide auto.
      * apply fin_idx_rel with (R := fun p (t : ntree n) => ⌊t⌋ₙ ≤ 1 + idx2nat p); eauto.
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

  (* We project TREE_n_pwc to get (Friedman) TREE(n) *)

  Definition Friedman_TREE := proj1_sig TREE_n_pwc.

  Theorem Friedman_TREE_spec m : m ≤ Friedman_TREE ↔ TREE_n_spec m.
  Proof. apply (proj2_sig TREE_n_pwc). Qed.

End Friedman_TREE.

Print ntree.
Print ltree.
Check ntree_size_fix.
Print list_sum.

Check Friedman_TREE.
Check Friedman_TREE_spec.
Print Assumptions Friedman_TREE_spec.


