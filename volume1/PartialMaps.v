Module PartialMap.
Require Import PeanoNat.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
  intro x. destruct x. simpl. assert (H: n=? n = true).
  { induction n as [|n' IHn']. simpl. reflexivity. simpl. rewrite -> IHn'. reflexivity. }
  rewrite -> H. reflexivity. Qed.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d x v. simpl. rewrite <- eqb_id_refl. reflexivity. Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d x y o. intro H. simpl. rewrite -> H. reflexivity. Qed. 

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

