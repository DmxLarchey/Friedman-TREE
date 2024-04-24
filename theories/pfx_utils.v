(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq 
  Require Import Arith Lia List Utf8.

From KruskalTrees
  Require Import idx vec.

From KruskalAfProp
  Require Import base notations almost_full.

Import ListNotations vec_notations.

Set Implicit Arguments.

Fact rev_pfx_rev_vec_list_eq X (f : nat → X) n :
          rev (pfx_rev f n) = vec_list (vec_set (λ i : idx n, f (idx2nat i))).
Proof.
  revert f; induction n as [ | n IHn ]; intros f; f_equal; auto.
  rewrite pfx_rev_S, rev_app_distr, IHn; auto.
Qed.

Fact good_rev_vec_list X (R : rel₂ X) n (v : vec X n) :
       good R (rev (vec_list v)) → ∃ i j, idx2nat i < idx2nat j ∧ R v⦃i⦄ v⦃j⦄.
Proof.
   intros (l & y & k & x & r & H1 & H2)%good_iff_split.
   apply f_equal with (f := @rev _) in H2; revert H2.
   rewrite rev_involutive; repeat (rewrite rev_app_distr; simpl); rewrite !app_ass.
   generalize (rev r) (rev k) (rev l); clear l k r; intros l k r; intros H2.
   destruct vec_list_split_inv with (1 := H2) as (p & H3 & H4).
   rewrite <- app_ass, <- app_ass in H2.
   destruct vec_list_split_inv with (1 := H2) as (q & H5 & H6).
   exists p, q; split; auto.
   + rewrite H4, H6, app_ass, !app_length; simpl; lia.
   + subst; auto.
Qed.
