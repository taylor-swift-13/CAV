Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition int_max : Z := 2147483647.

Fixpoint ex_nth_prime_has_divisor_from (x d : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      if Z.leb x (d * d) then false
      else if Z.eqb (Z.rem x d) 0 then true
      else ex_nth_prime_has_divisor_from x (d + 1) fuel'
  end.

Definition ex_nth_prime_is_prime (x : Z) : bool :=
  if Z.leb x 1 then
    false
  else
    negb (ex_nth_prime_has_divisor_from x 2 (Z.to_nat x)).

Definition ex_nth_prime_count_upto (x : Z) : Z :=
  let fix go (fuel : nat) : Z :=
      match fuel with
      | O => 0
      | S fuel' =>
          let y := Z.of_nat fuel' + 1 in
          go fuel' + if ex_nth_prime_is_prime y then 1 else 0
      end
  in go (Z.to_nat x).

Definition ex_nth_prime_value_spec (n r : Z) : Prop :=
  1 <= n /\
  2 <= r <= int_max /\
  ex_nth_prime_is_prime r = true /\
  ex_nth_prime_count_upto r = n /\
  (forall y,
      0 <= y < r ->
      ex_nth_prime_is_prime y = true ->
      ex_nth_prime_count_upto y < n).

Definition ex_nth_prime_value_pre (n : Z) : Prop :=
  1 <= n /\
  exists r, ex_nth_prime_value_spec n r.
