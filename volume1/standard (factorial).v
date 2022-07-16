Definition ltb (n m : nat) : bool
  . Admitted.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Admitted.
Example test_ltb2: (ltb 2 4) = true.
Admitted.
Example test_ltb3: (ltb 4 2) = false.
Admitted.

