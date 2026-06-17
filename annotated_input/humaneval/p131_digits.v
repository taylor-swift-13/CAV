Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Lists.List Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* spec/131 *)
(* def digits(n):
"""Given a positive integer n, return the product of the odd digits.
Return 0 if all digits are even.
For example:
digits(1) == 1
digits(4) == 0
digits(235) == 15
"""*)

Fixpoint get_digits_helper (n fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: get_digits_helper (n / 10) f'
    end
  end.

Definition get_digits (n : nat) : list nat :=
  get_digits_helper n n.

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_impl (n : nat) : nat :=
  let ds := filter Nat.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

(* n 为正整数 *)


Local Open Scope Z_scope.

Definition problem_131_pre (n : Z) : Prop := n > 0.
Fixpoint tail_odd_prod_fuel (fuel : nat) (n prod has : Z) : Z :=
  match fuel with
  | O => if Z.eqb has 0 then 0 else prod
  | S fuel' =>
      if Z.leb n 0 then if Z.eqb has 0 then 0 else prod
      else
        let d := Z.rem n 10 in
        if Z.odd d
        then tail_odd_prod_fuel fuel' (Z.quot n 10) (prod * d) 1
        else tail_odd_prod_fuel fuel' (Z.quot n 10) prod has
  end.

Definition tail_odd_prod (n : Z) : Z :=
  tail_odd_prod_fuel (Z.to_nat n) n 1 0.

Definition digits_state (n prod has : Z) : Z :=
  tail_odd_prod_fuel (Z.to_nat n) n prod has.

Definition problem_131_spec (n r : Z) : Prop :=
  n > 0 /\ r = digits_state n 1 0.

Local Open Scope Z_scope.
