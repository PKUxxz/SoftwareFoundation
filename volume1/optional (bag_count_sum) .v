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

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Definition sum : bag -> bag -> bag :=  app.

Theorem bag_count_sum : forall (s1 s2:bag),
  count 0 (sum s1 s2) = (count 0 s1) + (count 0 s2).
Proof.
  intros s1 s2. induction s1 as [|h t IHs1].
  - simpl. reflexivity. 
  - induction h as [|n' IHn'].
    + simpl. rewrite -> IHs1. reflexivity.
    + simpl. rewrite -> IHs1. reflexivity.