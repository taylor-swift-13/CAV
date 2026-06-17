(* spec/106 *)
(* Implement the function f that takes n as a parameter,
and returns a list of size n, such that the value of the element at index i is the factorial of i if i is even
or the sum of numbers from 1 to i otherwise.
i starts from 1.
the factorial of i is the multiplication of the numbers from 1 to i (1 * 2 * ... * i).
Example:
f(5) == [1, 2, 6, 24, 15] *)

(* 引入 Coq 的自然数和列表库 *)
Require Import Nat.
Require Import List.
Require Import Factorial.
Import ListNotations.

(* n 为自然数，无额外约束 *)


Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

From AUXLib Require Import ListLib.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint triangular_nat (n : nat) : nat :=
  match n with
  | O => O
  | S k => triangular_nat k + S k
  end.

Definition problem_106_pre (n : Z) : Prop :=
  0 <= n.

Fixpoint triangular_fuel (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => 0
  | S fuel' => if Z.leb i 0 then 0 else triangular_fuel fuel' (i - 1) + i
  end.

Fixpoint factorial_fuel_106 (fuel : nat) (i : Z) : Z :=
  match fuel with
  | O => 1
  | S fuel' => if Z.leb i 1 then 1 else i * factorial_fuel_106 fuel' (i - 1)
  end.

Definition triangular (i : Z) : Z :=
  triangular_fuel (Z.to_nat i) i.

Definition factorial (i : Z) : Z :=
  factorial_fuel_106 (Z.to_nat i) i.

Definition f_elem (i : Z) : Z :=
  if Z.even i then factorial i else triangular i.

Definition f_seq (n : Z) : list Z :=
  map (fun i => f_elem (i + 1)) (Zseq 0 (Z.to_nat n)).

Definition problem_106_spec (n : Z) (out : list Z) : Prop :=
  0 <= n /\ out = f_seq n.

Definition f_seq_int_range (n : Z) : Prop :=
  forall i,
    1 <= i <= n ->
    INT_MIN <= i <= INT_MAX /\
    INT_MIN <= triangular i <= INT_MAX /\
    INT_MIN <= factorial i <= INT_MAX.

Lemma triangular_0 :
  triangular 0 = 0.
Proof. reflexivity. Qed.

Lemma factorial_0 :
  factorial 0 = 1.
Proof. reflexivity. Qed.

Lemma triangular_step : forall i,
  0 <= i ->
  triangular (i + 1) = triangular i + (i + 1).
Proof.
  intros i Hi.
  unfold triangular.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (i + 1 <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (i + 1 - 1) with i by lia.
  reflexivity.
Qed.

Lemma factorial_step : forall i,
  0 <= i ->
  factorial (i + 1) = factorial i * (i + 1).
Proof.
  intros i Hi.
  destruct (Z.eq_dec i 0) as [-> | Hnz].
  - reflexivity.
  - unfold factorial.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    simpl.
    replace (i + 1 <=? 1) with false by (symmetry; apply Z.leb_gt; lia).
    replace (i + 1 - 1) with i by lia.
    ring.
Qed.

Lemma f_seq_Zlength : forall n,
  0 <= n ->
  Zlength (f_seq n) = n.
Proof.
  intros n Hn.
  unfold f_seq.
  rewrite Zlength_correct.
  rewrite length_map, Zseq_length.
  lia.
Qed.

Lemma f_seq_Znth : forall n i,
  0 <= i < n ->
  Znth i (f_seq n) 0 = f_elem (i + 1).
Proof.
  intros n i Hi.
  unfold f_seq.
  unfold Znth.
  eapply nth_error_nth.
  rewrite nth_error_map.
  rewrite nth_error_nth' with (d := 0%Z).
  - rewrite Zseq_nth by lia.
    rewrite Z2Nat.id by lia.
    reflexivity.
  - rewrite Zseq_length.
    lia.
Qed.

Lemma f_seq_sublist_snoc : forall n i,
  0 <= i < n ->
  sublist 0 (i + 1) (f_seq n) =
  sublist 0 i (f_seq n) ++ f_elem (i + 1) :: nil.
Proof.
  intros n i Hi.
  pose proof (f_seq_Zlength n ltac:(lia)) as Hlen.
  assert (Hsplit_lo : 0 <= 0 <= i) by lia.
  assert (Hsplit_hi : i <= i + 1 <= Zlength (f_seq n))
    by (rewrite Hlen; lia).
  rewrite (@sublist_split Z 0 (i + 1) i (f_seq n) Hsplit_lo Hsplit_hi).
  rewrite (sublist_single 0 i (f_seq n)).
  - rewrite f_seq_Znth by lia.
    reflexivity.
  - rewrite Hlen.
    lia.
Qed.

Lemma f_elem_even_rem : forall i,
  Z.rem i 2 = 0 ->
  f_elem i = factorial i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma f_elem_odd_rem : forall i,
  Z.rem i 2 <> 0 ->
  f_elem i = triangular i.
Proof.
  intros i Hrem.
  unfold f_elem.
  rewrite Zeven_rem.
  apply Z.eqb_neq in Hrem.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma problem_106_spec_f_seq : forall n,
  0 <= n ->
  problem_106_spec n (f_seq n).
Proof.
  intros n Hn.
  unfold problem_106_spec.
  split; [lia | reflexivity].
Qed.
