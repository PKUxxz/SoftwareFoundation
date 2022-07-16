Require Import PeanoNat.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint beq_nat n m : bool :=
  match n, m with
    | O, O => true
    | O, S _ => false
    | S _, O => false
    | S n1, S m1 => beq_nat n1 m1
  end.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
    | [ ] => 0
    | x :: xs =>
        match (beq_nat x v) with
          | true  => 1 + count v xs
          | false => count v xs
        end
  end.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | h :: t =>
        match (beq_nat h v) with
          | true  => t
          | false => h :: (remove_one v t)
        end
  end.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  -
    simpl. reflexivity.
  -
    simpl. rewrite IHn'. reflexivity. Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intro s. induction s as [|h t IHs'].
  - simpl. reflexivity.
  - induction h as [| n IHn]. simpl. rewrite -> leb_n_Sn. reflexivity. simpl. rewrite -> IHs'. reflexivity. Qed.