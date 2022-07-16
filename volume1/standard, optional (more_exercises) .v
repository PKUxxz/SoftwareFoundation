
Require Import PeanoNat.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Theorem leb_refl : forall n:nat,
  true = (n <=? n).
Proof.
  intro n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem zero_nbeq_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  intro n. simpl. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intro b. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p. intro H. induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity. 
  - simpl. rewrite -> IHp'. reflexivity. Qed.

Theorem S_nbeq_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  intro n. simpl. reflexivity. Qed.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intro n. simpl. rewrite -> plus_n_O. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c. destruct b.
  - simpl. destruct c. simpl. reflexivity. simpl. reflexivity.
  - simpl. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intro n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n']. 
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. rewrite plus_assoc. reflexivity. Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity. Qed.