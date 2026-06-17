(* spec/78 *)

(* def hex_key(num):
"""You have been tasked to write a function that receives
a hexadecimal number as a string and counts the number of hexadecimal
digits that are primes (prime number, or a prime, is a natural number
greater than 1 that is not a product of two smaller natural numbers).
Hexadecimal digits are 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, A, B, C, D, E, F.
Prime numbers are 2, 3, 5, 7, 11, 13, 17,...
So you have to determine a number of the following digits: 2, 3, 5, 7,
B (=decimal 11), D (=decimal 13).
Note: you may assume the input is always correct or empty string,
and symbols A,B,C,D,E,F are always uppercase.
Examples:
For num = "AB" the output should be 1.
For num = "1077E" the output should be 2.
For num = "ABED1A33" the output should be 4.
For num = "123456789ABCDEF0" the output should be 6.
For num = "2020" the output should be 2.
""" *)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_prime_hex (x : Z) : bool :=
  Z.eqb x 50 || Z.eqb x 51 || Z.eqb x 53 ||
  Z.eqb x 55 || Z.eqb x 66 || Z.eqb x 68.

Fixpoint count_prime_hex_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_prime_hex x then 1 else 0) + count_prime_hex_list xs
  end.

Definition count_prime_hex_upto (i : Z) (l : list Z) : Z :=
  count_prime_hex_list (firstn (Z.to_nat i) l).

Definition problem_78_pre (s : list Z) : Prop :=
  True.

Definition problem_78_spec (s : list Z) (output : Z) : Prop :=
  output = count_prime_hex_list s.

Lemma count_prime_hex_upto_0 : forall l,
  count_prime_hex_upto 0 l = 0.
Proof.
  intros l.
  unfold count_prime_hex_upto.
  reflexivity.
Qed.

Lemma count_prime_hex_list_app : forall l1 l2,
  count_prime_hex_list (l1 ++ l2) =
  count_prime_hex_list l1 + count_prime_hex_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma count_prime_hex_list_nonneg : forall l,
  0 <= count_prime_hex_list l.
Proof.
  induction l as [| x xs IH]; simpl.
  - lia.
  - destruct (is_prime_hex x); lia.
Qed.

Lemma firstn_succ_snoc_78 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_78 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_78 with (d := 0) by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.

Lemma is_prime_hex_true : forall x,
  x = 50 \/ x = 51 \/ x = 53 \/ x = 55 \/ x = 66 \/ x = 68 ->
  is_prime_hex x = true.
Proof.
  intros x Hx.
  unfold is_prime_hex.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | ->]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_prime_hex_false : forall x,
  x <> 50 -> x <> 51 -> x <> 53 -> x <> 55 -> x <> 66 -> x <> 68 ->
  is_prime_hex x = false.
Proof.
  intros x H50 H51 H53 H55 H66 H68.
  unfold is_prime_hex.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma count_prime_hex_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 50 \/ Znth i l 0 = 51 \/ Znth i l 0 = 53 \/
   Znth i l 0 = 55 \/ Znth i l 0 = 66 \/ Znth i l 0 = 68) ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_app.
  simpl.
  rewrite is_prime_hex_true by exact Hhit.
  simpl. lia.
Qed.

Lemma count_prime_hex_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 50 ->
  Znth i l 0 <> 51 ->
  Znth i l 0 <> 53 ->
  Znth i l 0 <> 55 ->
  Znth i l 0 <> 66 ->
  Znth i l 0 <> 68 ->
  count_prime_hex_upto (i + 1) l =
  count_prime_hex_upto i l.
Proof.
  intros i l Hi Hlt H50 H51 H53 H55 H66 H68.
  unfold count_prime_hex_upto.
  rewrite firstn_succ_Znth_78 by lia.
  rewrite count_prime_hex_list_app.
  simpl.
  rewrite is_prime_hex_false by auto.
  simpl. lia.
Qed.

Lemma problem_78_spec_intro : forall s output,
  ascii_range s ->
  output = count_prime_hex_upto (Zlength s) s ->
  problem_78_spec s output.
Proof.
  intros s output _ Hout.
  unfold problem_78_spec, count_prime_hex_upto in *.
  rewrite Hout.
  replace (Z.to_nat (Zlength s)) with (length s) by (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  reflexivity.
Qed.
