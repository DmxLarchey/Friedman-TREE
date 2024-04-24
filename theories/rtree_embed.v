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
  Require Import notations tactics list_utils ltree rtree.

From KruskalFinite
  Require Import finite decide examples.trees. (* examples is for finiteness wrt weight *)

From KruskalAfProp
  Require Import base notations almost_full.

From KruskalHigmanProp
  Require Import list_embed.

From KruskalThmProp
  Require Import ltree_embed kruskal_theorems.

Import ListNotations rtree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "l ≤ₕ m" (at level 70, no associativity, format "l  ≤ₕ  m").

Unset Elimination Schemes.

Inductive rtree_homeo_embed : rtree → rtree → Prop :=
  | rtree_homeo_embed_subt s t l : t ∈ l → s ≤ₕ t → s ≤ₕ ⟨l⟩ᵣ
  | rtree_homeo_embed_root l m : list_embed rtree_homeo_embed l m → ⟨l⟩ᵣ ≤ₕ ⟨m⟩ᵣ
where "s ≤ₕ t" := (rtree_homeo_embed s t).

Set Elimination Schemes.

Create HintDb rtree_db.

#[global] Hint Resolve rtree_size_gt : rtree_db.
#[global] Hint Constructors rtree_homeo_embed : rtree_db.

Section rtree_homeo_embed_ind.

  (* We implement the induction principle by hand because Coq
     currently does not manage nested schemes *)

  Variables (P : rtree → rtree → Prop)
            (HT1 : ∀ s t l, t ∈ l
                          → s ≤ₕ t
                          → P s t
                          → P s ⟨l⟩ᵣ)
            (HT2 : ∀ l m,   list_embed rtree_homeo_embed l m
                          → list_embed P l m
                          → P ⟨l⟩ᵣ ⟨m⟩ᵣ).

  Theorem rtree_homeo_embed_ind : ∀ s t, s ≤ₕ t → P s t.
  Proof.
    refine (fix loop s t D { struct D } := _).
    destruct D as [ s t l H1 H2 | l m H1 ].
    + apply HT1 with (1 := H1); trivial.
      apply loop, H2.
    + apply HT2; trivial.
      revert H1; induction 1; auto with list_db.
  Qed.

End rtree_homeo_embed_ind.

(* We deduce and right inversion lemma for s ≤ₕ ⟨l⟩ᵣ *)
Fact rtree_homeo_embed_inv_right s t :
          s ≤ₕ t
        ↔ match t with
          | ⟨l⟩ᵣ => (∃r, r ∈ l ∧ s ≤ₕ r)
                  ∨ match s with ⟨m⟩ᵣ => list_embed rtree_homeo_embed m l end
          end.
Proof.
  split.
  + induction 1; eauto.
  + destruct t; destruct s; intros [ (? & ? & ?) | ]; eauto with rtree_db.
Qed.

#[local] Hint Resolve in_map list_embed_map : core.

Theorem af_rtree_homeo_embed : af rtree_homeo_embed.
Proof.
  generalize (af_ltree_homeo_embed af_unit).
  af rel morph (λ x y, ltree_rtree x = y).
  + intros r; destruct (ltree_rtee_surj r) as (? & <-); eauto.
  + intros t1 t2 ? ? <- <-.
    induction 1; simpl; eauto with rtree_db.
Qed.

(* Embedded trees are smaller *)
Fact rtree_homeo_embed_size s t : s ≤ₕ t → ⌊s⌋ᵣ ≤ ⌊t⌋ᵣ.
Proof.
  induction 1 as [ s t l H1 H2 IH2 | l m H1 IH1 ] ; rewrite !rtree_size_fix.
  + apply list_sum_in with (f := rtree_size) in H1; lia.
  + apply le_n_S; revert IH1; clear H1.
    induction 1; simpl; tlia.
Qed.

#[local] Hint Resolve fin_rtree_size_eq fin_nat_le : core.

Corollary fin_rtree_size_lt n : fin (λ t, ⌊t⌋ᵣ < n).
Proof. apply fin_measure_lt with (n := S n); eauto. Qed.

Corollary fin_rtree_size_le n : fin (λ t, ⌊t⌋ᵣ ≤ n).
Proof. apply fin_measure_le with (n := S n); eauto. Qed.

#[local] Hint Resolve list_embed_decide : core.

(* Embedding of rtrees is a decidable property *)
Theorem rtree_homeo_embed_dec s t : { s ≤ₕ t } + { ~ s ≤ₕ t }.
Proof.
  induction t as [ l IHl ] in s |- *.
  decide eq (rtree_homeo_embed_inv_right s ⟨l⟩ᵣ).
  decide auto; fin auto.
  destruct s; auto.
Qed.

#[local] Hint Resolve fin_rtree_size_lt rtree_homeo_embed_dec : core.

(* There are finitely many trees homeo-embedding in t *)
Theorem fin_rtree_homeo_embed t : fin (λ s, s ≤ₕ t).
Proof.
  finite as (fun s => s ≤ₕ t /\ ⌊s⌋ᵣ < S ⌊t⌋ᵣ).
  2: finite dec left.
  intros s; split; try tauto; split; auto.
  apply le_n_S, rtree_homeo_embed_size; auto.
Qed.

