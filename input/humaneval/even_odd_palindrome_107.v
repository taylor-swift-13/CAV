(* spec/107 *)
(* Given a positive integer n, return a tuple that has the number of even and odd
integer palindromes that fall within the range(1, n), inclusive. *)

Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Fixpoint reverse_digits_loop (fuel : nat) (t r : Z) : Z :=
  match fuel with
  | O => r
  | S fuel' =>
      if t >? 0
      then reverse_digits_loop fuel' (t / 10) (r * 10 + t mod 10)
      else r
  end.

Definition is_palindrome (x : Z) : bool :=
  if x <=? 0 then false else reverse_digits_loop 4 x 0 =? x.

Definition is_even (x : Z) : bool :=
  x mod 2 =? 0.

Fixpoint count_even_pal_upto_nat (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
      let x := Z.of_nat (S k') in
      count_even_pal_upto_nat k' +
      if andb (is_palindrome x) (is_even x) then 1 else 0
  end.

Fixpoint count_odd_pal_upto_nat (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
      let x := Z.of_nat (S k') in
      count_odd_pal_upto_nat k' +
      if andb (is_palindrome x) (negb (is_even x)) then 1 else 0
  end.

Definition count_even_pal_upto (n : Z) : Z :=
  count_even_pal_upto_nat (Z.to_nat n).

Definition count_odd_pal_upto (n : Z) : Z :=
  count_odd_pal_upto_nat (Z.to_nat n).



From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Coq.micromega.Lia.

Import naive_C_Rules.

Definition problem_107_pre (n : Z) : Prop :=
  1 <= (n) <= 1000.

Definition problem_107_spec (n : Z) (output : list Z) : Prop :=
  (output = [count_even_pal_upto n; count_odd_pal_upto n]).

Definition is_pal (x : Z) : Z :=
  if is_palindrome x then 1 else 0.

Definition pal_reverse_loop_state (x t r : Z) : Prop :=
  1 <= x <= 1000 /\
  exists fuel : nat,
    0 <= t <= x /\
    ((fuel = 4%nat /\ r = 0) \/
     (fuel = 3%nat /\ 0 <= r <= 9) \/
     (fuel = 2%nat /\ 0 <= r <= 99) \/
     (fuel = 1%nat /\ 0 <= r <= 999) \/
     (fuel = 0%nat /\ 0 <= r <= 9999)) /\
    t < 10 ^ Z.of_nat fuel /\
    reverse_digits_loop fuel t r = reverse_digits_loop 4 x 0.

Definition pal_count_prefix (k n even_count odd_count : Z) : Prop :=
  0 <= k <= n /\
  even_count = count_even_pal_upto k /\
  odd_count = count_odd_pal_upto k.
