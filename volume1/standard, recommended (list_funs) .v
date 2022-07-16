Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil =>  nil
  | h :: t => 
            match h with
             |  O => (nonzeros t)
             |  S n => S n :: (nonzeros t)
            end
  end.


Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil =>  nil
  | h :: t => 
            match (oddb h) with
             |  true => h :: (oddmembers t)
             |  false => oddmembers t
            end
  end.

Compute(oddmembers [0;1;0;2;3;0;0]).

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Definition countoddmembers (l:natlist) : nat :=
  match l with
  | nil =>  O
  | h :: t => (length (oddmembers (h :: t)))
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.