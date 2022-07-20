From Coq Require Import
     Ascii
     Basics
     Decimal
     List
     String
     ZArith.

Import ListNotations.
Local Open Scope program_scope.
Local Open Scope string_scope.

Export Coq.Strings.String.StringSyntax.

(* This makes just the [%string] key available to [Derive Show]. *)
Delimit Scope string_scope with string.

Definition newline := String "010" ""%string.

Class Show (A : Type) : Type :=
{
  show : A -> string           
}.

Instance showBool : Show bool :=
  {
    show := fun b:bool => if b then "true" else "false"
  }.
Compute (show true).

Inductive primary := Red | Green | Blue.
Instance showPrimary : Show primary :=
  {
    show :=
      fun c:primary =>
        match c with
        | Red => "Red"
        | Green => "Green"
        | Blue => "Blue"
        end
  }.
Compute (show Green).

Fixpoint string_of_nat_aux (time n : nat) (acc : string) : string :=
  let d := match n mod 10 with
           | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3" | 4 => "4" | 5 => "5"
           | 6 => "6" | 7 => "7" | 8 => "8" | _ => "9"
           end in
  let acc' := d ++ acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => string_of_nat_aux time' n' acc'
      end
  end.
Definition string_of_nat (n : nat) : string :=
  string_of_nat_aux n n "".
Instance showNat : Show nat :=
  {
    show := string_of_nat
  }.
Compute (show 42).

Definition showPair_aux (p: nat * bool) :=
  match p with
    pair a b => show a ++ " " ++ show b 
  end.

Instance showPairNatBool : Show (nat * bool) :=
  {
    show :=
    fun p:nat * bool =>
      let (a,b) := p in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.

Compute (show (pair 2 true)).

Definition showOne {A : Type} `{Show A} (a : A) : string :=
  "The value is " ++ show a.
Compute (showOne true).
Compute (showOne (pair 2 true)).

Definition showTwo {A B : Type}
           `{Show A} `{Show B} (a : A) (b : B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.
Compute (showTwo true 42).
Compute (showTwo Red Green).

Class Eq A :=
  {
    eqb: A -> A -> bool;
  }.
Notation "x =? y" := (eqb x y) (at level 70).

Instance eqBool : Eq bool :=
  {
    eqb := fun (b c : bool) =>
       match b, c with
         | true, true => true
         | true, false => false
         | false, true => false
         | false, false => true
       end
  }.
Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.

(*boolArrowBool*)


Instance showPair {A B : Type} `{Show A} `{Show B} : Show (A * B) :=
  {
    show p :=
      let (a,b) := p in
        "(" ++ show a ++ "," ++ show b ++ ")"
  }.
Compute (show (true,42)).

Instance eqPair {A B : Type} `{Eq A} `{Eq B} : Eq (A * B) :=
  {
    eqb p1 p2 :=
      let (p1a,p1b) := p1 in
      let (p2a,p2b) := p2 in
      andb (p1a =? p2a) (p1b =? p2b)
  }.

Fixpoint showListAux {A : Type} (s : A -> string) (l : list A) : string :=
  match l with
    | nil => ""
    | cons h nil => s h
    | cons h t => append (append (s h) ", ") (showListAux s t)
  end.
Instance showList {A : Type} `{Show A} : Show (list A) :=
  {
    show l := append "[" (append (showListAux show l) "]")
  }.

Compute (show [1;2;3]).

(*eqEx*)
Fixpoint eqlist {A: Type} `{Eq A} (l1 l2: list A): bool :=
  match l1 with
    |nil => match l2 with
            |nil => true
            |cons h2 t2 => false
            end
    |cons h1 t1 => match l2 with
                   | nil => false
                   | cons h2 t2 => andb (eqb h1 h2) (eqlist t1 t2)
                   end
  end.

Instance eqList {A: Type} `{Eq A} : Eq (list A) :=
  {
    eqb := eqlist                           
  }.

Print option.
Compute (Some 3).

Instance showOption {A: Type} `{Show A}: Show (option A) :=
  {
    show := fun o:option A => match o with
  | None => "None"
  | Some a => "Some " ++ show a
  end
  }.

Compute (show (Some 4)).

Instance eqOption {A: Type} `{Eq A}: Eq (option A) :=
  {
    eqb :=
    fun o1 o2:option A =>
      match o1 with
      | None => match o2 with
                | None => true
                | Some a2 => false
                end
      | Some a1 => match o2 with
                   | None => false
                   | Some a2 => eqb a1 a2
                   end
      end
                          
  }.

Compute (eqb (Some 4) (Some 4)).
(*/eqEx*)

Class OrdBad A :=
  {
    eqbad : A -> A -> bool;
    lebad : A -> A -> bool
  }.




