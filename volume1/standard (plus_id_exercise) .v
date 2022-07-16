Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros m n o. intros H1 H2. rewrite -> H1,H2. reflexivity. Qed.
