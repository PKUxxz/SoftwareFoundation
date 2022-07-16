Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  |Z => B Z
  |A n => B n
  |B n => A (incr n)
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | A n =>2 * (bin_to_nat n)
  | B n =>2 * (bin_to_nat n) + 1
  end.
Theorem plus_1_Sn : forall n : nat,
  S n = n +1.
Proof.
  intro n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed. 
  
Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat(incr b) = S(bin_to_nat b).
Proof.
  intro b. induction b as [|b' IHb'|b' IHb'].
  - simpl. reflexivity.
  - simpl. rewrite <- plus_1_Sn. reflexivity.
  - simpl. rewrite <- plus_n_O. rewrite <- plus_n_O. 
    rewrite -> IHb'. rewrite <- plus_1_Sn. 
    assert (H : forall a b : nat, S a + S b = S (S (a + b))).
    intros a b. induction a as [|a' IHa']. reflexivity. simpl. rewrite <- IHa'. reflexivity.
    rewrite -> H. reflexivity. Qed.