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

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l. induction l as [|h t IHl'].
  - simpl. reflexivity. 
  - simpl. rewrite -> IHl'. reflexivity. Qed.
  
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

Theorem app_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [|h t IHl'].
  - simpl. rewrite -> app_nil. reflexivity.
  - simpl. rewrite -> IHl'. rewrite -> app_three. reflexivity. Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intro l. induction l as [|h t IHl'].
   - simpl. reflexivity. 
   - simpl. rewrite -> app_rev. rewrite -> IHl'. simpl. reflexivity. Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite -> app_three. rewrite -> app_three. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with 
  |nil => nil
  |h :: t => match h with
             |O => (nonzeros t)
             |S n => h :: (nonzeros t)
             end
  end.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1 as [|h t IHl'].
  - simpl. reflexivity.
  - destruct h. simpl. rewrite -> IHl'. reflexivity. 
    simpl. rewrite -> IHl'. reflexivity. Qed.



