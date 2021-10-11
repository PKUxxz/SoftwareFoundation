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

(*standard (or_distributes_over_and)*)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  - intros [HP | [HQ HR]].
    + split; left; apply HP.
    + split; right; try (apply HQ); try (apply HR).
  - intros [[HPl | HQ] [HPr | HR]].
    + left. apply HPl.
    + left. apply HPl.
    + left. apply HPr.
    + right. split. apply HQ. apply HR.
Qed.
(*/standard (or_distributes_over_and)*)

From Coq Require Import Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].   exists (2 + m).
  apply Hm. Qed.

(*standard, recommended (dist_not_exists)*)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not. intros X P A. intros [x NP]. apply NP. apply A.
Qed.
(*/standard, recommended (dist_not_exists)*)

(*standard (dist_exists_or)*)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
 intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.
(*/standard (dist_exists_or)*)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  -
    simpl. intros [].
  -
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(*standard (In_map_iff)*)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [| h t IHt].
    + simpl. intros [].
    + simpl. intros [H1 | H2].
      * exists h. split. apply H1. left. reflexivity.
      * apply IHt in H2. destruct H2 as [w [F I]]. exists w. split.
        apply F. right. apply I.
  - intros [x [H1 H2]]. rewrite <- H1. apply In_map. apply H2. Qed.
(*/standard (In_map_iff)*)

(*standard (In_app_iff)*)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  - induction l as [|h t IHt].
    + simpl. intro H. right. apply H.
    + simpl. intros [H1 | H2]. left. left. apply H1. apply IHt in H2. 
      destruct H2 as [H3 | H4]. left. right. apply H3. right. apply H4.
  - induction l as [| h t IHt]. 
    + intros [H1 | H2]. destruct H1. simpl. apply H2.
    + simpl. intros [[H1 | H2] | H3]. 
      * left. apply H1.
      * right. apply IHt. left. apply H2.
      * right. apply IHt. right. apply H3.
Qed.
(*/standard (In_app_iff)*)

(*standard, recommended (All)*)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l. split.
  - (*(forall x : T, In x l -> P x) -> All P l*)
    induction l as [|h t IHt].
    + intro H. simpl. reflexivity.
    + intro H. simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHt. intros x H1. apply H. simpl. right. apply H1.
  - (*All P l -> forall x : T, In x l -> P x*)
    induction l as [|h t IHt].
    + intros. destruct H0.
    + simpl. intros [H1 H2] x [H3|H4].
      * rewrite <- H3. apply H1.
      * apply IHt. apply H2. apply H4. 
Qed. 
(*/standard, recommended (All)*)

(*standard (combine_odd_even)*)
Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n =>
    match oddb n with
    | true => Podd n
    | false => Peven n
    end.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n. destruct (oddb n) eqn:H.
  - intros H1 H2. unfold combine_odd_even. rewrite -> H. apply H1. reflexivity.
  - intros H1 H2. unfold combine_odd_even. rewrite -> H. apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n. unfold combine_odd_even. 
  intros H1 H2. rewrite -> H2 in H1. apply H1. 
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n. unfold combine_odd_even. intros H1 H2.
  rewrite -> H2 in H1. apply H1.
Qed.
(*/standard (combine_odd_even)*)











