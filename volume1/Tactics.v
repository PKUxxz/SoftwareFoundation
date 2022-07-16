Set Warnings "-notation-overridden,-parsing".
From LF Require Export Poly.
Require Import PeanoNat.

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

 (* standard, optional (silly_ex) *)
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
  intros eq1 eq2. apply eq2. Qed. 
 (*  /standard, optional (silly_ex) *)

 (* standard (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' eq. symmetry. rewrite -> eq. Search rev. apply rev_involutive. Qed. 
 (* /standard (apply_exercise1) *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. Qed.
 
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2. Qed.


 (* standard, optional (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof. 
  intros n m o p eq1 eq2. apply trans_eq with m.
  apply eq2. apply eq1. Qed.
 (*  /standard, optional (apply_with_exercise) *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm. Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.


 (*  standard (injection_ex3) *)
Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j eq1 eq2.
  injection eq2. intros h1 h2. symmetry. apply h2. Qed.
 (*  /standard (injection_ex3) *)

Theorem eqb_0_l : forall n, 
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. Qed.

(*standard (discriminate_ex3)*)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H. discriminate H. Qed.
(* /standard (discriminate_ex3)*)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. Qed.

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.


(*standard, recommended (plus_n_n_injective)*)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - intros m H. induction m as [| m'].
    + reflexivity.
    + discriminate H.
  - intros m H. induction m as [| m'].
    + discriminate H.
    + simpl in H. rewrite <- plus_n_Sm in H. rewrite <- plus_n_Sm in H. 
      inversion H. apply IHn' in H1. rewrite -> H1. reflexivity. Qed.  
(*plus_n_Sm: forall n m : nat, S (n + m) = n + S m*)
(*/standard, recommended (plus_n_n_injective)*)

 (* standard (eqb_true)*) 
Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intro n. induction n as [|n' IHn'].
  - intros m H. induction m as [| m' IHm'].
    + reflexivity.
    + inversion H.
  - intros m H. induction m as [| m' IHm'].
    + inversion H.
    + inversion H. apply IHn' in H. rewrite -> H. reflexivity. Qed.
 (*  /standard (eqb_true)*)


 (*standard, recommended (gen_dep_practice)*)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l as [| h t IH].
  - intros.
    rewrite <- H.
    reflexivity.
  - intros.
    rewrite <- H.
    simpl.
    apply IH.
    reflexivity.
Qed.
 (* /standard, recommended (gen_dep_practice)*)

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - reflexivity.
    - destruct (n =? 5) eqn:E2.
      + reflexivity.
      + reflexivity. Qed.

 (*standard, optional (combine_split)*)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem tail_eq: forall (X: Type) (h: X) (l1 l2: list X),
    l1 = l2 -> h :: l1 = h :: l2.
Proof.
  intros. apply f_equal. apply H.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| h t IHt].
  - intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2 H. inversion H. destruct h. destruct (split t).
    simpl in H1. inversion H1. simpl. 
    apply tail_eq.
    apply IHt.
    reflexivity.
Qed.
 (* /standard, optional (combine_split)*)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3).
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
    - apply eqb_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    -
     
      destruct (n =? 5) eqn:Heqe5.
        +
          apply eqb_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + discriminate eq. Qed.

(*standard (destruct_eqn_practice)*)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct b eqn:H.
  - destruct (f true) eqn:H1.
    + rewrite -> H1. rewrite -> H1. reflexivity.
    + destruct (f false) eqn:H2.
      rewrite -> H1. reflexivity.
      rewrite -> H2. reflexivity.
  - destruct (f false) eqn:H3.
    + destruct (f true) eqn:H4.
      rewrite -> H4. reflexivity.
      rewrite -> H3. reflexivity.
    + rewrite -> H3. rewrite -> H3. reflexivity.
Qed. 
(* /standard (destruct_eqn_practice)*)

(*standard (eqb_sym)*)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m. destruct m as [|m'].
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intro m. destruct m as [|m'].
    + simpl. reflexivity.
    + simpl. apply IHn'. 
Qed.
(*/standard (eqb_sym)*)

(*standard, optional (eqb_trans)*)

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - destruct m, p.
    + reflexivity.  (*(n,m,p)=(0,0,0)*)
    + discriminate. (*(n,m,p)=(0,0,S p)*)
    + discriminate. (*(n,m,p)=(0,S m,0)*)
    + discriminate. (*(n,m,p)=(0,S m,S p)*)
  - destruct m, p.
    + discriminate.
    + discriminate.
    + discriminate.
    + simpl. apply IHn'.
Qed. 
 
(*/standard, otional (eqb_trans)*)

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y l1. induction l1 as [|h1 t1 IHt1].
  - intro l2. induction l2 as [|h2 t2 IHt2].
    + reflexivity.
    + simpl. discriminate.
  - intros l2 H. induction l2 as [|h2 t2 IHt2].
    + simpl. discriminate.
    + simpl. rewrite  -> (IHt1 t2). 
      * reflexivity.
      * simpl in H. inversion H. reflexivity.
Qed.
(*/advanced (split_combine)*)

(*advanced (filter_exercise)*)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x.
  induction l as [| h t].
  - intros. inversion H.
  - intros. simpl in H.
    destruct (test h) eqn:TH.
    + inversion H. rewrite <- H1. apply TH.
    + apply IHt in H. apply H.
Qed.
(*/advanced (filter_exercise)*)

(*forall_exists_challenge*)
Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => true
  | h :: t => andb (test h) (forallb test t)
  end. 

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. simpl. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. simpl. reflexivity. Qed.

Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. simpl. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | nil => false
  | h :: t => orb (test h) (existsb test t)
  end.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. simpl. reflexivity. Qed.

Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_existsb_4 : existsb evenb [] = false.
Proof. simpl. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros X test l. unfold existsb'. induction l as [|h t IHt].
  - simpl. reflexivity.
  - simpl. destruct (test h) eqn:E.
    + reflexivity.
    + simpl. apply IHt.
Qed.
(*/forall_exists_challenge*)

