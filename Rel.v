Set Warnings "-notation-overridden,-parsing".
From LF Require Export Indprop.

Definition relation (X: Type) := X -> X -> Prop.

Print le.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Print next_nat.
Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity. Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.

Inductive total_relation : nat -> nat -> Prop :=
  | tr : forall n m, total_relation n m.

Inductive empty_relation : nat -> nat -> Prop := .

(*optional (total_relation_not_partial)*)
Theorem total_relation_not_a_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply (Hc 0).
    - apply tr.
    - apply tr. }
  discriminate Nonsense. Qed.
(*/optional (total_relation_not_partial)*)

(*optional (empty_relation_partial)*)
Theorem empty_relation_not_a_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function. intros x y1 y2 H1 H2.
  inversion H1. Qed.
(*/optional (empty_relation_partial)*)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - apply Hnm.
  - apply le_S. apply IHHmo. Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(*optional (le_trans_hard_way)*)
Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
Qed.
(*/optional (le_trans_hard_way)*)

(*standard, optional (lt_trans'')*)
Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_S. inversion Hmo. 
    + rewrite <- H0. apply Hnm.
    + apply IHo'. apply H0. 
Qed.  
(*/standard, optional (lt_trans'')*)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

(*standard, optional (le_S_n)*)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply le_Sn_le. apply H1.
Qed.
(*/standard, optional (le_S_n)*)

(*standard, optional (le_Sn_n)*)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. induction n as [|n' IHn'].
  - intro H. inversion H.
  - intro H. apply IHn'. apply le_S_n. apply H.
Qed. 
(*/standard, optional (le_Sn_n)*)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(*standard, optional (le_not_symmetric)*)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold not. unfold symmetric. intros H.
  assert (N: 1 <= 0 -> False).
  { apply (le_Sn_n 0). }
  apply N. apply H. apply le_S. apply le_n.
Qed.
(*/standard, optional (le_not_symmetric)*)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(*standard, optional (le_antisymmetric)*)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  induction a as [|a'].
  - (* a = 0 *)
    intros b ab ba.
    inversion ba as [E|].
    reflexivity.
  - (* a = S a' *)
    intros b ab ba.
    inversion ab as [E | b' H H'].
    + (* a = b *)
      reflexivity.
    + (* a < b *)
      cut (a' = b').
      * intros E. rewrite E. reflexivity.
      * apply IHa'. 
        { apply le_Sn_le. apply H. }
        { apply le_S_n. rewrite H'. apply ba. }
Qed.
(*/standard, optional (le_antisymmetric)*)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - apply le_reflexive.
    - split.
      + apply le_antisymmetric.
      + apply le_trans. Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  -
    intro H. induction H.
    + apply rt_refl.
    +
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  -
    intro H. induction H.
    + inversion H. apply le_S. apply le_n.
    + apply le_n.
    +
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.



