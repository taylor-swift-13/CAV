Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import FunInd.
From AUXLib Require Import ListLib.
Require Import base_conversion_lib.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_15_pre (n : Z) : Prop :=
  True.

Fixpoint sequence_prefix_nat (count : nat) : list Z :=
  match count with
  | O => []
  | S O => base_digits 0 10
  | S count' => sequence_prefix_nat count' ++ 32 :: base_digits (Z.of_nat count') 10
  end.

Definition sequence_prefix (i : Z) : list Z :=
  sequence_prefix_nat (Z.to_nat i).

Definition sequence_output (n : Z) : list Z :=
  sequence_prefix (n + 1).

Definition problem_15_spec (n : Z) (output : list Z) : Prop :=
  output = sequence_output n.

Definition sequence_output_bound (n : Z) : Prop :=
  Zlength (sequence_output n) + 1 <= 12 * (n + 1) + 1.

Lemma p015_sequence_prefix_1 :
  sequence_prefix 1 = [48].
Proof.
  unfold sequence_prefix.
  simpl.
  rewrite base_digits_equation.
  reflexivity.
Qed.

Lemma p015_sequence_prefix_step : forall i,
  1 <= i ->
  sequence_prefix (i + 1) = sequence_prefix i ++ 32 :: base_digits i 10.
Proof.
  intros i Hi.
  unfold sequence_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  destruct (Z.to_nat i) as [| k] eqn:Hk; [lia |].
  assert (i = Z.of_nat (S k)) as -> by lia.
  simpl.
  reflexivity.
Qed.

Lemma p015_Forall_Znth_nonzero : forall l p,
  Forall (fun x => x <> 0) l ->
  0 <= p < Zlength l ->
  Znth p l 0 <> 0.
Proof.
  intros l p Hforall Hp.
  unfold Znth.
  apply Forall_forall with (x := nth (Z.to_nat p) l 0) in Hforall.
  - exact Hforall.
  - apply nth_In.
    rewrite Zlength_correct in Hp.
    lia.
Qed.

Lemma p015_base_digits_10_nonzero_forall : forall n,
  Forall (fun x => x <> 0) (base_digits n 10).
Proof.
  intro n.
  functional induction (base_digits n 10).
  - constructor; [lia | constructor].
  - constructor; [lia | constructor].
  - constructor.
    + match goal with
      | H : (n <=? 0)%Z = false |- _ =>
          apply Z.leb_gt in H; lia
      end.
    + constructor.
  - apply Forall_app.
    split.
    + match goal with
      | IH : Forall (fun x : Z => x <> 0) (base_digits (n / base) base) |- _ =>
          exact IH
      end.
    + constructor.
      * match goal with
        | Hbase : (base <=? 1)%Z = false |- _ =>
            apply Z.leb_gt in Hbase;
            pose proof (Z.mod_pos_bound n base ltac:(lia));
            lia
        end.
      * constructor.
Qed.

Lemma p015_sequence_prefix_nat_nonzero_forall : forall count,
  Forall (fun x => x <> 0) (sequence_prefix_nat count).
Proof.
  induction count as [| count IH]; simpl.
  - constructor.
  - destruct count as [| count']; simpl.
    + apply p015_base_digits_10_nonzero_forall.
    + apply Forall_app.
      split.
      * exact IH.
      * repeat constructor; try lia.
        apply p015_base_digits_10_nonzero_forall.
Qed.

Lemma p015_sequence_prefix_nonzero_forall : forall i,
  Forall (fun x => x <> 0) (sequence_prefix i).
Proof.
  intro i.
  unfold sequence_prefix.
  apply p015_sequence_prefix_nat_nonzero_forall.
Qed.

Lemma p015_sequence_prefix_step_Znth_nonzero : forall i p,
  0 <= p < Zlength (sequence_prefix i ++ 32 :: base_digits i 10) ->
  Znth p (sequence_prefix i ++ 32 :: base_digits i 10) 0 <> 0.
Proof.
  intros i p Hp.
  apply p015_Forall_Znth_nonzero.
  - apply Forall_app.
    split.
    + apply p015_sequence_prefix_nonzero_forall.
    + repeat constructor; try lia.
      apply p015_base_digits_10_nonzero_forall.
  - exact Hp.
Qed.
