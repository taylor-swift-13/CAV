Require Import ZArith.

Open Scope Z_scope.

Fixpoint ex_allergies_score_count_aux (score : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      ex_allergies_score_count_aux score k +
      Z.rem (Z.div score (2 ^ Z.of_nat k)) 2
  end.

Definition ex_allergies_score_count_spec (score : Z) : Z :=
  snd (Z.iter 8
    (fun st =>
       let '(i, count) := st in
       (i + 1, count + Z.rem (Z.div score (2 ^ i)) 2))
    (0, 0)).
