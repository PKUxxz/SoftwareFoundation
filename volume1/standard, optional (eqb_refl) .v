Require Import PeanoNat.

Theorem eqb_refl : forall n : nat,
  true = (n =? n).
Proof.
  intro n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite->IHn'. reflexivity. Qed.