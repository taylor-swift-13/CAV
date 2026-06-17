(* spec/46 *)
(* The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4_nat(0) -> 0
fib4_nat(1) -> 0
fib4_nat(2) -> 2
fib4_nat(3) -> 0
fib4_nat(n) -> fib4_nat(n-1) + fib4_nat(n-2) + fib4_nat(n-3) + fib4_nat(n-4).
Please write a function to efficiently compute the n-th element of the fib4_nat number sequence. Do not use recursion.
>>> fib4_nat(5)
4
>>> fib4_nat(6)
8
>>> fib4_nat(7)
14 *)

(*
  Spec(input : int, output : int) :=

​	∃ Fib : list int,
​		Fib[0] = 0 /\ Fib[1] = 0 /\ Fib[2] = 2 /\ Fib[3] = 0 /\
​		∀i ∈ N, i >3 → Fib[i] = Fib[i-1] + Fib[i-2] + Fib[i-3] + Fib[i-4] /\
​		output = Fib[input] *)

Require Import Coq.Arith.Arith.

(* 使用 Fixpoint 表示 fib4_nat 序列 *)
Fixpoint fib4_nat (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
    match n1 with
    | 0 => 0
    | S n2 =>
      match n2 with
      | 0 => 2
      | S n3 =>
        match n3 with
        | 0 => 0
        | S n4 => fib4_nat n1 + fib4_nat n2 + fib4_nat n3 + fib4_nat n4
        end
      end
    end
  end.



Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Fixpoint fib4_fuel (fuel : nat) (n : Z) : Z :=
  match fuel with
  | O =>
      if Z.eqb n 2 then 2 else 0
  | S fuel' =>
      if Z.eqb n 0 then 0
      else if Z.eqb n 1 then 0
      else if Z.eqb n 2 then 2
      else if Z.eqb n 3 then 0
      else fib4_fuel fuel' (n - 1) + fib4_fuel fuel' (n - 2) +
           fib4_fuel fuel' (n - 3) + fib4_fuel fuel' (n - 4)
  end.

Definition fib4 (n : Z) : Z :=
  fib4_fuel (Z.to_nat n) n.

Definition problem_46_pre (n : Z) : Prop :=
  0 <= n.

Definition problem_46_spec (n output : Z) : Prop :=
  0 <= n /\ output = fib4 n.

Definition fib4_step_int_range (n : Z) : Prop :=
  forall i,
    4 <= i <= n ->
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) <= INT_MAX /\
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) + fib4 (i - 2) <= INT_MAX /\
    INT_MIN <= fib4 (i - 4) + fib4 (i - 3) + fib4 (i - 2) + fib4 (i - 1) <= INT_MAX.

Lemma fib4_fuel_nat :
  forall (n fuel : nat),
    (n <= fuel)%nat ->
    fib4_fuel fuel (Z.of_nat n) = Z.of_nat (fib4_nat n).
Proof.
  apply (well_founded_induction
           lt_wf
           (fun m => forall fuel : nat,
              (m <= fuel)%nat ->
              fib4_fuel fuel (Z.of_nat m) = Z.of_nat (fib4_nat m))).
  intros m IH fuel Hle.
  destruct fuel as [| fuel]; [destruct m; [reflexivity | lia] |].
  destruct m as [| [| [| [| n]]]]; cbn [fib4_fuel fib4_nat]; try reflexivity.
  remember (Z.of_nat (S (S (S (S n))))) as z eqn:Hz.
  change
    (fib4_fuel (S fuel) z =
     Z.of_nat (fib4_nat (S (S (S n))) + fib4_nat (S (S n)) +
               fib4_nat (S n) + fib4_nat n)).
  cbn [fib4_fuel fib4_nat].
  assert (Hz0 : (z =? 0)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz1 : (z =? 1)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz2 : (z =? 2)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  assert (Hz3 : (z =? 3)%Z = false) by (apply Z.eqb_neq; subst z; lia).
  rewrite Hz0, Hz1, Hz2, Hz3.
  replace (z - 1) with (Z.of_nat (S (S (S n)))) by (subst z; lia).
  replace (z - 2) with (Z.of_nat (S (S n))) by (subst z; lia).
  replace (z - 3) with (Z.of_nat (S n)) by (subst z; lia).
  replace (z - 4) with (Z.of_nat n) by (subst z; lia).
  rewrite (IH (S (S (S n))) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH (S (S n)) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH (S n) ltac:(lia) fuel ltac:(lia)).
  rewrite (IH n ltac:(lia) fuel ltac:(lia)).
  simpl fib4_nat.
  repeat rewrite Nat2Z.inj_add.
  reflexivity.
Qed.

Lemma fib4_original_spec :
  forall n, 0 <= n -> fib4 n = Z.of_nat (fib4_nat (Z.to_nat n)).
Proof.
  intros n Hn.
  unfold fib4.
  replace (fib4_fuel (Z.to_nat n) n) with
    (fib4_fuel (Z.to_nat n) (Z.of_nat (Z.to_nat n))).
  2:{ rewrite Z2Nat.id by lia. reflexivity. }
  apply fib4_fuel_nat.
  lia.
Qed.

Lemma fib4_recurrence :
  forall n, 4 <= n ->
    fib4 n = fib4 (n - 1) + fib4 (n - 2) + fib4 (n - 3) + fib4 (n - 4).
Proof.
  intros n Hn.
  rewrite !fib4_original_spec by lia.
  replace (Z.to_nat (n - 1)) with (Z.to_nat n - 1)%nat by lia.
  replace (Z.to_nat (n - 2)) with (Z.to_nat n - 2)%nat by lia.
  replace (Z.to_nat (n - 3)) with (Z.to_nat n - 3)%nat by lia.
  replace (Z.to_nat (n - 4)) with (Z.to_nat n - 4)%nat by lia.
  assert (Hnat_ge : (4 <= Z.to_nat n)%nat) by lia.
  destruct (Z.to_nat n) as [| [| [| [| k]]]]; try lia.
  replace (S (S (S (S k))) - 1)%nat with (S (S (S k))) by lia.
  replace (S (S (S (S k))) - 2)%nat with (S (S k)) by lia.
  replace (S (S (S (S k))) - 3)%nat with (S k) by lia.
  replace (S (S (S (S k))) - 4)%nat with k by lia.
  simpl fib4_nat.
  repeat rewrite Nat2Z.inj_add.
  lia.
Qed.

Lemma problem_46_spec_base_0 :
  problem_46_spec 0 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.

Lemma problem_46_spec_base_1 :
  problem_46_spec 1 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.

Lemma problem_46_spec_base_2 :
  problem_46_spec 2 2.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.

Lemma problem_46_spec_base_3 :
  problem_46_spec 3 0.
Proof.
  unfold problem_46_spec, fib4. simpl. lia.
Qed.
