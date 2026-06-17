(* spec/70 *)
(* def strange_sort_list(lst):
'''
Given list of integers, return list in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum and so on.

Examples:
strange_sort_list([1, 2, 3, 4]) == [1, 4, 2, 3]
strange_sort_list([5, 5, 5, 5]) == [5, 5, 5, 5]
strange_sort_list([]) == []
''' *)
(* 引入 Coq 标准库以使用列表、自然数和置换等概念 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.

(* 引入列表的标准表示法，如 [] 和 x :: xs *)
Import ListNotations.
Open Scope Z_scope.

Fixpoint remove_one (x : Z) (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if Z.eqb x h then t else h :: remove_one x t
  end.

Fixpoint list_min (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_min t with
    | None => Some h
    | Some m => Some (Z.min h m)
    end
  end.

Fixpoint list_max (l : list Z) : option Z :=
  match l with
  | [] => None
  | h :: t =>
    match list_max t with
    | None => Some h
    | Some m => Some (Z.max h m)
    end
  end.

Fixpoint strange_sort_aux (l : list Z) (fuel : nat) (is_min : bool) : list Z :=
  match fuel with
  | 0%nat => []
  | S n =>
    match l with
    | [] => []
    | _ =>
      match if is_min then list_min l else list_max l with
      | None => []
      | Some v => v :: strange_sort_aux (remove_one v l) n (negb is_min)
      end
    end
  end.

Definition strange_sort_list (l : list Z) : list Z :=
  strange_sort_aux l (length l) true.



Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition problem_70_pre (l : list Z) : Prop :=
  True.

Definition problem_70_spec (input output : list Z) : Prop :=
  (output = strange_sort_list input).

Definition sorted_int_list_by (ascending : Z) (l : list Z) : Prop :=
  if Z.eqb ascending 0 then True else Sorted Z.le l.

Fixpoint copy_prefix_nat (n : nat) (input : list Z) : list Z :=
  match n with
  | O => []
  | S n' => copy_prefix_nat n' input ++ [Znth (Z.of_nat n') input 0]
  end.

Definition copy_prefix (n : Z) (input : list Z) : list Z :=
  copy_prefix_nat (Z.to_nat n) input.

Definition strange_index (size i : Z) : Z :=
  if Z.eqb (Z.rem i 2) 0
  then i ÷ 2
  else size - 1 - (i ÷ 2).

Fixpoint strange_output_prefix_nat (size : Z) (n : nat) (sorted_l : list Z) : list Z :=
  match n with
  | O => []
  | S n' =>
      strange_output_prefix_nat size n' sorted_l ++
      [Znth (strange_index size (Z.of_nat n')) sorted_l 0]
  end.

Definition strange_output_prefix (size i : Z) (sorted_l : list Z) : list Z :=
  strange_output_prefix_nat size (Z.to_nat i) sorted_l.

Definition strange_output (size : Z) (sorted_l : list Z) : list Z :=
  strange_output_prefix size size sorted_l.


(* Ground-truth proof helpers. *)
Lemma copy_prefix_Zlength : forall n input,
  0 <= n ->
  Zlength (copy_prefix n input) = n.
Proof.
  intros n input Hn.
  unfold copy_prefix.
  rewrite Zlength_correct.
  replace n with (Z.of_nat (Z.to_nat n)) at 2 by lia.
  revert input.
  induction (Z.to_nat n); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn0.
  lia.
Qed.

Lemma copy_prefix_0 : forall input,
  copy_prefix 0 input = [].
Proof.
  reflexivity.
Qed.

Lemma copy_prefix_snoc : forall i input,
  0 <= i ->
  copy_prefix (i + 1) input = copy_prefix i input ++ [Znth i input 0].
Proof.
  intros i input Hi.
  unfold copy_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma sublist_snoc_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  sublist 0 (i + 1) l = sublist 0 i l ++ [Znth i l 0].
Proof.
  intros l i Hi.
  rewrite Zlength_correct in Hi.
  pose proof (sublist_split 0 (i + 1) i l ltac:(lia) ltac:(rewrite ?Zlength_correct; lia)) as Hsplit.
  rewrite Hsplit.
  rewrite (sublist_single 0 i l) by (rewrite ?Zlength_correct; lia).
  reflexivity.
Qed.

Lemma copy_prefix_eq_sublist_nat : forall n input,
  Z.of_nat n <= Zlength input ->
  copy_prefix (Z.of_nat n) input = sublist 0 (Z.of_nat n) input.
Proof.
  induction n as [| n IH]; intros input Hle.
  - reflexivity.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite copy_prefix_snoc by lia.
    rewrite sublist_snoc_Znth by lia.
    rewrite IH by lia.
    reflexivity.
Qed.

Lemma copy_prefix_eq_sublist : forall input i,
  0 <= i <= Zlength input ->
  copy_prefix i input = sublist 0 i input.
Proof.
  intros input i Hi.
  replace i with (Z.of_nat (Z.to_nat i)) by lia.
  apply copy_prefix_eq_sublist_nat.
  lia.
Qed.

Lemma copy_prefix_full : forall input,
  copy_prefix (Zlength input) input = input.
Proof.
  intros input.
  pose proof (Zlength_nonneg input).
  rewrite copy_prefix_eq_sublist by lia.
  apply sublist_self.
  reflexivity.
Qed.

Lemma strange_output_prefix_Zlength : forall size i sorted_l,
  0 <= i ->
  Zlength (strange_output_prefix size i sorted_l) = i.
Proof.
  intros size i sorted_l Hi.
  unfold strange_output_prefix.
  rewrite Zlength_correct.
  replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia.
  revert size sorted_l.
  induction (Z.to_nat i); intros; simpl; [reflexivity |].
  rewrite app_length.
  simpl.
  rewrite Nat2Z.inj_add.
  simpl.
  rewrite IHn.
  lia.
Qed.

Lemma strange_output_prefix_0 : forall size sorted_l,
  strange_output_prefix size 0 sorted_l = [].
Proof.
  reflexivity.
Qed.

Lemma strange_output_prefix_snoc : forall size i sorted_l,
  0 <= i ->
  strange_output_prefix size (i + 1) sorted_l =
  strange_output_prefix size i sorted_l ++ [Znth (strange_index size i) sorted_l 0].
Proof.
  intros size i sorted_l Hi.
  unfold strange_output_prefix.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma strange_index_even : forall size i,
  Z.rem i 2 = 0 ->
  strange_index size i = i ÷ 2.
Proof.
  intros size i Hrem.
  unfold strange_index.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma strange_index_odd : forall size i,
  Z.rem i 2 <> 0 ->
  strange_index size i = size - 1 - i ÷ 2.
Proof.
  intros size i Hrem.
  unfold strange_index.
  destruct (Z.eqb_spec (Z.rem i 2) 0); [contradiction | reflexivity].
Qed.

Lemma strange_output_full : forall size sorted_l,
  strange_output size sorted_l = strange_output_prefix size size sorted_l.
Proof.
  reflexivity.
Qed.

Lemma sorted_full_Znth : forall full_l sorted_l size idx,
  0 <= idx < size ->
  sublist 0 size full_l = sorted_l ->
  Znth idx full_l 0 = Znth idx sorted_l 0.
Proof.
  intros full_l sorted_l size idx Hidx Hsub.
  rewrite <- Hsub.
  rewrite Znth_sublist0 by lia.
  reflexivity.
Qed.

Lemma quot2_bounds : forall size i,
  0 <= size ->
  0 <= i ->
  i < size ->
  0 <= i ÷ 2 < size.
Proof.
  intros size i Hsize Hi Hlt.
  assert (Hq : i ÷ 2 = i / 2) by (apply Z.quot_div_nonneg; lia).
  rewrite Hq.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma reverse_quot2_bounds : forall size i,
  0 <= size ->
  0 <= i ->
  i < size ->
  0 <= size - 1 - i ÷ 2 < size.
Proof.
  intros size i Hsize Hi Hlt.
  pose proof (quot2_bounds size i Hsize Hi Hlt) as [Hq0 Hqlt].
  split; lia.
Qed.
