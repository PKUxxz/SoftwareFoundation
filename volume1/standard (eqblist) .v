Require Import PeanoNat.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint eq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => eq_nat n1 m1
  end.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with
  | nil, nil => true
  | nil, l2 => false
  | l1, nil => false
  | a :: l1', b :: l2' =>
    match (eq_nat a b) with
    |true => eqblist l1' l2'
    |false => false
    end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem nat_equals_self :forall n:nat,
  eq_nat n n = true.
Proof. 
  intro n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intro l. induction l as [|h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> nat_equals_self. rewrite -> IHl'. reflexivity. Qed.