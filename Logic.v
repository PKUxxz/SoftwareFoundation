Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Check 3 = 3.

Check forall n m : nat, n + m = m + n.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

Check @eq.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

 (* standard (and_exercise)*)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m. induction n as [|n' IHn'].
  - intro H. split. simpl in H. reflexivity. apply H.
  - simpl. intro H. inversion H.
Qed.
 (* /standard (and_exercise)*)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. Qed.

(*standard, optional (proj2)*)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. Qed.
(*/standard, optional (proj2)*)

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP. Qed.

(*standard (and_assoc)*)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. 
  - split.
    + apply HP.
    + apply HQ.
  - apply HR. Qed.
(*/standard (and_assoc)*)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  -
    rewrite Hn. reflexivity.
  -
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(*standard (mult_eq_0)*)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. destruct n as [|n'].
  - left. reflexivity.
  - destruct m as [|m'].
    + right. reflexivity.
    + inversion H.
  Qed.
(*/standard (mult_eq_0)*)

(*standard (or_commut)*)
Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
  Qed.
(*/standard (or_commut)*)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra. Qed.

(*standard, optional (not_implies_our_not)*)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros. apply H in H0. destruct H0. Qed. 
(*/standard, optional (not_implies_our_not)*)

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not. intros contra. discriminate contra. Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H. unfold not. intros G. apply G. apply H. Qed.

(*standard, recommended (contrapositive)*)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H. unfold not. intros G I. apply H in I. apply G in I. destruct I. Qed.
(*/standard, recommended (contrapositive)*)

(*standard (not_both_true_and_false)*)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intro P. unfold not. intros [H1 H2]. apply H2 in H1. destruct H1. Qed.
(*/standard (not_both_true_and_false)*)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  -
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  -
    unfold not in H.
    exfalso.     apply H. reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB. Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  intros b. split.
  - apply not_true_is_false.
  -
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

(*standard, optional (iff_properties)*)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intro P. reflexivity. Qed.
  

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R [PQ QP] [QR RQ]. split.
  - (* P -> R *)
    intros HP. apply QR. apply PQ. apply HP.
  - (* R -> P*)
    intros HR. apply QP. apply RQ. apply HR. Qed.
(*/standard, optional (iff_properties)*)










