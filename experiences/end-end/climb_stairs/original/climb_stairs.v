Require Import ZArith.

Open Scope Z_scope.

Fixpoint climb_stairs_pair (fuel : nat) : Z * Z :=
  match fuel with
  | O => (1, 1)
  | S k =>
      let p := climb_stairs_pair k in
      (snd p, fst p + snd p)
  end.

Definition climb_stairs_nat (n : nat) : Z :=
  fst (climb_stairs_pair n).

Definition climb_stairs_z (n : Z) : Z :=
  climb_stairs_nat (Z.to_nat n).
