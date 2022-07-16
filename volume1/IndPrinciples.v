Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

Check nat_ind.

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - reflexivity.
  - simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.

(*standard, optional (plus_one_r')*)
Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n H. simpl. rewrite -> H. reflexivity. Qed.
(*/standard, optional (plus_one_r')*)

Inductive yesno : Type :=
  | yes
  | no.

Check yesno_ind.

(*standard, optional (rgb)*)
(*forall P : rgb -> Prop, P red -> P green -> P blue -> forall y : rgb, P y*)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.
(*/standard, optional (rgb)*)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind.

(*standard, optional (natlist1)*)
(*forall P : natlist1 -> Prop,
       P nnil1 ->
       (forall l : natlist1, P l -> forall n : nat, P (nsnoc1 l n)) ->
       forall n : natlist1, P n*)
Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).

Check natlist1_ind.
(*/standard, optional (natlist1)*)

(*standard, optional (byntree_ind)*)
(*forall P : byntree -> Prop,
       P bempty ->
       (forall yn : yesno, P (bleaf yn)) ->
       (forall (yn : yesno) (t1 : byntree),
        P t1 -> forall t2 : byntree, P t2 -> P (nbranch yn t1 t2)) ->
       forall b : byntree, P b*)
Inductive byntree : Type :=
 | bempty
 | bleaf (yn : yesno)
 | nbranch (yn : yesno) (t1 t2 : byntree).

Check byntree_ind.
(*/standard, optional (byntree_ind)*)

(*standard, optional (ex_set)*)
Inductive ExSet : Type := 
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.
(*/standard, optional (ex_set)*)

(*standard, optional (tree)*)
(*forall (X : Type) (P : tree X -> Prop),
       (forall x : X, P (leaf X x)) ->
       (forall t1 : tree X, P t1 -> forall t2 : tree X, P t2 -> P (node X t1 t2)) ->
       forall t : tree X, P t*)
Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.
(*/standard, optional (tree)*)

(*standard, optional (mytype)*)
Inductive mytype (X: Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).
Check mytype_ind.
(*/standard, optional (mytype)*)

(*standard, optional (foo)*)
Inductive foo (X:Type) (Y:Type) :=
  | bar (x : X) 
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).

Check foo_ind.
(*/standard, optional (foo)*)

(*standard, optional (foo')*)
Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.

Check foo'_ind.
(*/standard, optional (foo')*)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Definition P_m0r' : nat->Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - unfold P_m0r. simpl. reflexivity.
  - intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  - reflexivity.
  -
    
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Inductive even : nat -> Prop := 
| ev_0 : even 0 
| ev_SS : forall n : nat, even n -> even (S (S n)).

Check even_ind.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem ev_ev' : forall n, even n -> even' n.
Proof.
  apply even_ind.
  -
    apply even'_0.
  -
    intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Check le_ind.





