(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Utf8.

From KruskalTrees
  Require Import tactics list_utils idx ltree ntree.

From KruskalFinite
  Require Import finite decide examples.trees. (* examples is for finiteness wrt weight *)

From KruskalAfProp
  Require Import base notations almost_full.

From KruskalHigmanProp
  Require Import list_embed.

From KruskalThmProp
  Require Import ltree_embed kruskal_theorems.

Import ListNotations ltree_notations ntree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "l '≤ₕ' m" (at level 70, no associativity, format "l  ≤ₕ  m").

#[global] Hint Constructors ltree_product_embed ltree_homeo_embed : ltree_db.

Definition ltree_size {X} : ltree X → nat := ltree_weight (λ _, 1).

Fact ltree_size_fix X x l : @ltree_size X ⟨x|l⟩ₗ = 1+list_sum ltree_size l.
Proof. apply ltree_weight_fix. Qed.

#[local] Notation "⌊ t ⌋ₗ" := (ltree_size t) (at level 0, t at level 200, format "⌊ t ⌋ₗ").

#[local] Hint Resolve eq_nat_dec : core.

Fact fin_ltree_size_eq X : finite X → ∀n, fin (λ t : ltree X, ⌊t⌋ₗ = n).
Proof. intros ? n; apply fin_ltree_weight with (n := S n); fin auto. Qed.

#[local] Hint Resolve fin_ltree_size_eq : core.

Fact fin_ltree_size_le X : finite X → ∀n, fin (λ t : ltree X, ⌊t⌋ₗ ≤ n).
Proof. intros Hx n; apply fin_measure_le with (n := S n); auto. Qed.

Section ltree_homeo_embed_dec_fin.

  Variables (X : Type) (R : rel₂ X).

  Infix "≤ₕ" := (ltree_homeo_embed R).

  Implicit Type t : ltree X.

  Fact ltree_homeo_embed_size s t : s ≤ₕ t → ⌊s⌋ₗ ≤ ⌊t⌋ₗ.
  Proof.
    induction 1 as [ s t p l Hl H IH
                   | p l q m E H IH ];
      rewrite !ltree_size_fix.
    + apply list_sum_in with (f := ltree_size) in Hl; lia.
    + apply le_n_S; revert IH; clear H.
      induction 1; simpl; tlia.
  Qed.

  Fact ltree_homeo_embed_inv_right s t :
          s ≤ₕ t
        ↔ match t with
          | ⟨q|m⟩ₗ => (∃r, r ∈ m ∧ s ≤ₕ r)
                    ∨ match s with
                      | ⟨p|l⟩ₗ => R p q ∧ list_embed (ltree_homeo_embed R) l m
                      end
          end.
  Proof.
    split.
    + induction 1; subst; eauto; right; eauto.
    + destruct t as [ q m ]; destruct s as [ p l ].
      intros [ (r & H1 & H2) | (? & ?) ]; eauto with ltree_db.
  Qed.

  Hypothesis Rdec : ∀ x y, decider (R x y).

  Hint Resolve list_embed_decide : core.

  Theorem ltree_homeo_embed_dec s t : decider (s ≤ₕ t).
  Proof.
    revert s; induction t as [ q m IHm ]; intros [ p l ].
    decide eq (ltree_homeo_embed_inv_right ⟨p|l⟩ₗ ⟨q|m⟩ₗ).
    decide auto; fin auto.
  Qed.

  Hypothesis HX : finite X.

  Hint Resolve fin_ltree_size_le
               ltree_homeo_embed_size
               ltree_homeo_embed_dec : core.

  (* There are finitely many ltrees embedded into t *)

  Corollary fin_ltree_homeo_embed t : fin (λ s, s ≤ₕ t).
  Proof.
    finite as (fun s => s ≤ₕ t /\ ⌊s⌋ₗ <= ⌊t⌋ₗ).
    + split; eauto; tauto.
    + finite dec left; auto.
  Qed.

End ltree_homeo_embed_dec_fin.

Section ntree_homeo_embed_dec_fin.

  Variable n : nat.

  (* Finitely branching trees labeled in idx n ≃ {1,...,n} *)

  Implicit Type t : ntree n.

  Definition ntree_homeo_embed : rel₂ (ntree n) := ltree_homeo_embed (@eq _).

  Theorem af_ntree_homeo_embed : af ntree_homeo_embed.
  Proof. apply af_ltree_homeo_embed, af_idx. Qed.

  Fact fin_ntree_size_eq a : fin (λ t, ⌊t⌋ₙ = a).
  Proof. apply fin_ltree_size_eq; fin auto. Qed.

  Fact fin_ntree_size_le a : fin (λ t, ⌊t⌋ₙ ≤ a).
  Proof. apply fin_ltree_size_le; fin auto. Qed.

  Hint Resolve idx_eq_dec : core.

  Infix "≤ₕ" := ntree_homeo_embed.

  Fact ntree_homeo_embed_size s t : s ≤ₕ t → ⌊s⌋ₙ ≤ ⌊t⌋ₙ.
  Proof. apply ltree_homeo_embed_size. Qed.

  Fact ntree_homeo_embed_dec s t : { s ≤ₕ t } + { ¬ s ≤ₕ t }.
  Proof. revert s t; apply ltree_homeo_embed_dec; auto. Qed.

  Theorem fin_ntree_homeo_embed t : fin (λ s, s ≤ₕ t).
  Proof. apply fin_ltree_homeo_embed; fin auto. Qed.

End ntree_homeo_embed_dec_fin.

Arguments ntree_homeo_embed {n}.

