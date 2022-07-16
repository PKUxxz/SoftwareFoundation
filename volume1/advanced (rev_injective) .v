Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem app_nil : forall l : natlist,
  l ++ [ ] = l.
Proof. 
  intro l. induction l as [|h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Theorem app_three : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof. 
  intros l1 l2 l3. induction l1 as [|h t IHl1].
  - simpl. reflexivity. 
  - simpl. rewrite -> IHl1. reflexivity. Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|h t IHl1'].
  - simpl. rewrite -> app_nil. reflexivity. 
  - simpl. rewrite -> IHl1'. rewrite -> app_three. reflexivity. Qed. 

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l. induction l as [| h' t' IHl'].
  - simpl. reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity. Qed.

Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intro H. rewrite <- rev_involutive. rewrite <- H. 
  rewrite -> rev_involutive.  reflexivity. Qed.