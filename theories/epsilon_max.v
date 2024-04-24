(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia ConstructiveEpsilon Utf8.

Section epsilon_smallest_new.

  Variables (P : nat → Prop)
            (Pdec : ∀n, { P n } + { ~ P n })
            (exP  : ∃n, P n).

  (* This is a cumbersome proof aimed to be compatible
     with both ConstructiveEpsilon <= 8.14.* and >= 8.15.* *)
  Local Lemma epsilon_smallest_new : { n | P n ∧ ∀k, P k → n ≤ k }.
  Proof.
    destruct epsilon_smallest with (2 := exP)
      as (n & H1 & H2); auto.
    exists n; split; [ auto | ].
    intros k Hk.
    destruct (le_lt_dec n k); auto;
      apply H2 in Hk; tauto.
  Qed.

End epsilon_smallest_new.

Section maximal.

  Variables (P : nat → Prop)
            (Pdec : ∀n, { P n } + { ~ P n })
            (Pzero : P 0)
            (Pmon : ∀ i j, i ≤ j → P j → P i)
            (Pnot : ∃n, ¬ P n).

  (** Computes the maximal value n such that P(n) holds
      for a bounded monotonic and decidable predicate *)

  Theorem epsilon_maximal : { n | ∀i, i ≤ n ↔ P i }.
  Proof.
    apply epsilon_smallest_new in Pnot as (n & H1 & H2).
    + exists (n-1); intros i; split; intros Hi.
      * destruct (Pdec i) as [ | H3 ]; auto.
        apply H2 in H3.
        destruct n; (lia || easy).
      * destruct (le_lt_dec n i) as [ H | H ].
        - destruct H1; revert Hi; apply Pmon; auto.
        - destruct n; try tauto; lia.
    + intros n; destruct (Pdec n); tauto.
  Qed.

End maximal.
