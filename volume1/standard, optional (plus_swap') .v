Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity. 
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed. 

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm. rewrite <- plus_assoc.
  replace (p+n) with (n+p). reflexivity. rewrite plus_comm. reflexivity. Qed.
