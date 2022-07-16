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

