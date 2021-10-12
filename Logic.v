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

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction m as [| m' IHm'].
  - (* m = 0 *)
    simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *)
    simpl. rewrite <- IHm'. rewrite <- plus_n_Sm.
    reflexivity.  Qed.

Check plus_comm.

Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

(*standard (tr_rev_correct)*)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X. apply functional_extensionality. unfold tr_rev. induction x as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite <- IHt. Admitted.
(*/standard (tr_rev_correct)*)

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

(*standard (evenb_double_conv)*)
Lemma  evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof. 
  intro n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. assert(H: forall b:bool, b=negb(negb b)). 
    intro b. destruct b;reflexivity. apply H. Qed.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intro n. induction n as [|n' IHn'].
  - simpl. exists 0. reflexivity.
  - destruct IHn' as [m IHm]. destruct (evenb n') eqn:H.
    + rewrite -> evenb_S. rewrite -> H. simpl. rewrite -> IHm. 
      exists m. reflexivity. 
    + rewrite -> evenb_S. rewrite -> H. simpl. rewrite -> IHm. exists (S m).
      simpl. reflexivity. Qed. 
(*/standard (evenb_double_conv)*)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Require Import PeanoNat.

(* standard (logical_connectives)*)
Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - destruct b1 eqn:H. 
    + intro H1. split. reflexivity. simpl in H1. apply H1.
    + intro H1. inversion H1.
  - intros [H1 H2]. rewrite -> H1. rewrite -> H2. reflexivity. Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - destruct b1 eqn:H.
    + intro H1. left. reflexivity.
    + intro H1. simpl in H1. right. apply H1.
  - intros [H1|H2].
    + rewrite -> H1. reflexivity.
    + rewrite -> H2. destruct b1 eqn:H.
      * reflexivity.
      * reflexivity.
Qed.
(* /standard (logical_connectives)*)

(*standard (eqb_neq)*)
Theorem eqb_refl: forall n: nat,
  true = (n =? n).
Proof.
  induction n as [|n' IH].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem eqb_eq:
  forall n1 n2: nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros x y.
  rewrite <- not_true_iff_false.
  rewrite <- eqb_eq.
  reflexivity.
Qed.
(*/standard (eqb_neq)*)

(*standard (eqb_list)*)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | _, [] => false
  | [], _ => false
  | h1 :: t1, h2 :: t2 => andb (eqb h1 h2) (eqb_list eqb t1 t2)
  end.

Lemma eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb H. induction l1 as [|h1 t1 IHt1].
  - induction l2 as [| h2 t2 IHt2].
    + split. 
      * simpl. intro H1. reflexivity.
      * simpl. intro H1. reflexivity.
    + split.
      * simpl. intro H1. discriminate H1.
      * simpl. intro H1. discriminate H1.
  - induction l2 as [| h2 t2 IHt2].
    + split.
      * simpl. intro H1. discriminate H1.
      * simpl. intro H1. discriminate H1.
    + split.
      * simpl. intro H1. apply andb_true_iff in H1. destruct H1 as [H2 H3].
        apply H in H2. apply IHt1 in H3. rewrite -> H2. rewrite -> H3. reflexivity.
      * simpl. intro H1. apply andb_true_iff. split.
        apply H. inversion H1. reflexivity. apply IHt1. inversion H1. reflexivity. 
Qed. 
(*/standard (eqb_list)*)

(*standard, recommended (All_forallb)*)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.  
  intros X test l. split.
  - induction l as [|h t IHt].
    + simpl. reflexivity.
    + simpl. intro H. split.
      * apply andb_true_iff in H. destruct H as [H1 H2]. apply H1.
      * apply IHt. apply andb_true_iff in H. destruct H as [H1 H2]. apply H2.
  - induction l as [|h t IHt].
    + simpl. reflexivity.
    + simpl. intros [H1 H2]. apply andb_true_iff. split.
      * apply H1.
      * apply IHt. apply H2.
Qed.
(*/standard, recommended (All_forallb)*)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. discriminate contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (n =? m)).
  symmetry.
  apply eqb_eq.
Qed.

(*standard (excluded_middle_irrefutable)*)
Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P H.
  unfold not in H.
  apply H.
  right.
  intros HP.
  apply H.
  left.
  apply HP.
Qed.
(*/standard (excluded_middle_irrefutable)*)

(* Exercise 20 *)
Theorem not_exists_dist:
  excluded_middle ->
  forall (X: Type) (P: X -> Prop),
    ~(exists x, ~P x) -> (forall x, P x).
Proof.
  intros EM X P.
  unfold not.
  intros H.
  intros x.

  destruct (EM (P x)) as [EM1 | EM2].
  - apply EM1.
  - exfalso. apply H.
    exists x.
    apply EM2.
Qed.

(* Exercise 21 *)
(* Definition excluded_middle := forall P: Prop, P \/ ~P. *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P: Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q: Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q: Prop,
  (P -> Q) -> (~P \/ Q).

Fact dne_eq_lem: double_negation_elimination <-> excluded_middle.
Proof.
  split.
  - intros dne.
    intros P.
    apply dne.
    apply excluded_middle_irrefutable.
  - intros lem.
    intros P H.
    destruct (lem P) as [lem1 | lem2].
    + apply lem1.
    + destruct (H lem2).
Qed.

Fact dmnn_eq_lem: de_morgan_not_and_not <-> excluded_middle.
Proof.
  split.
  - intros dmnn.
    intros P.
    apply dmnn.
    intros [H1 H2].
    destruct (H2 H1).
  - intros lem.
    intros P Q H.
    destruct (lem P) as [H1 | H2].
    + left. apply H1.
    + destruct (lem Q) as [H3 | H4].
      * right. apply H3.
      * exfalso. apply H.
        split. apply H2. apply H4.
Qed.















