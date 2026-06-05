Require Import ZArith.

Open Scope Z_scope.

Fixpoint count_multiples_upto (k : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S n =>
      count_multiples_upto k n +
      (if Z.eq_dec (Z.rem (Z.of_nat (S n)) k) 0 then 1 else 0)
  end.

Definition count_multiples_spec (n k : Z) : Z :=
  count_multiples_upto k (Z.to_nat n).
Definition count_multiples_upto_z (k i : Z) : Z :=
  count_multiples_upto k (Z.to_nat i).

Lemma count_multiples_spec_as_upto_z :
  forall n k, count_multiples_spec n k = count_multiples_upto_z k n.
Proof.
  reflexivity.
Qed.
