(* spec/64 *)

(* def vowels_count(s):
"""Write a function vowels_count which takes a string representing
a word as input and returns the number of vowels in the string.
Vowels in this case are 'a', 'e', 'i', 'o', 'u'. Here, 'y' is also a
vowel, but only when it is at the end of the given word.

Example:
>>> vowels_count("abcde")
2
>>> vowels_count("ACEDY")
3
""" *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.

Definition is_regular_vowel (x : Z) : bool :=
  Z.eqb x 97 || Z.eqb x 101 || Z.eqb x 105 || Z.eqb x 111 || Z.eqb x 117 ||
  Z.eqb x 65 || Z.eqb x 69 || Z.eqb x 73 || Z.eqb x 79 || Z.eqb x 85.

Definition is_y (x : Z) : bool :=
  Z.eqb x 121 || Z.eqb x 89.

Fixpoint count_regular_vowels_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if is_regular_vowel x then 1 else 0) + count_regular_vowels_list xs
  end.

Definition count_regular_vowels_upto (i : Z) (l : list Z) : Z :=
  count_regular_vowels_list (firstn (Z.to_nat i) l).

Definition last_y_add (l : list Z) : Z :=
  let n := Zlength l in
  if Z.eqb n 0 then 0
  else if is_y (Znth (n - 1) l 0) then 1 else 0.

Definition problem_64_pre (s : list Z) : Prop :=
  True.

Definition problem_64_spec (s : list Z) (output : Z) : Prop :=
  output = count_regular_vowels_list s + last_y_add s.

Lemma count_regular_vowels_upto_0 : forall l,
  count_regular_vowels_upto 0 l = 0.
Proof.
  intros l.
  unfold count_regular_vowels_upto.
  reflexivity.
Qed.

Lemma count_regular_vowels_list_app : forall l1 l2,
  count_regular_vowels_list (l1 ++ l2) =
  count_regular_vowels_list l1 + count_regular_vowels_list l2.
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma firstn_succ_snoc_64 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.

Lemma firstn_succ_Znth_64 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_64 with (d := 0) by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.

Lemma is_regular_vowel_true : forall x,
  x = 97 \/ x = 101 \/ x = 105 \/ x = 111 \/ x = 117 \/
  x = 65 \/ x = 69 \/ x = 73 \/ x = 79 \/ x = 85 ->
  is_regular_vowel x = true.
Proof.
  intros x Hx.
  unfold is_regular_vowel.
  destruct Hx as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    repeat rewrite Z.eqb_refl; reflexivity.
Qed.

Lemma is_regular_vowel_false : forall x,
  x <> 97 -> x <> 101 -> x <> 105 -> x <> 111 -> x <> 117 ->
  x <> 65 -> x <> 69 -> x <> 73 -> x <> 79 -> x <> 85 ->
  is_regular_vowel x = false.
Proof.
  intros x H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold is_regular_vowel.
  repeat match goal with
  | |- context[Z.eqb ?a ?b] =>
      replace (Z.eqb a b) with false by (symmetry; apply Z.eqb_neq; lia)
  end.
  reflexivity.
Qed.

Lemma count_regular_vowels_upto_step_hit : forall i l,
  0 <= i ->
  i < Zlength l ->
  (Znth i l 0 = 97 \/ Znth i l 0 = 101 \/ Znth i l 0 = 105 \/
   Znth i l 0 = 111 \/ Znth i l 0 = 117 \/
   Znth i l 0 = 65 \/ Znth i l 0 = 69 \/ Znth i l 0 = 73 \/
   Znth i l 0 = 79 \/ Znth i l 0 = 85) ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l + 1.
Proof.
  intros i l Hi Hlt Hhit.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_app.
  simpl.
  rewrite is_regular_vowel_true by exact Hhit.
  simpl. lia.
Qed.

Lemma count_regular_vowels_upto_step_miss : forall i l,
  0 <= i ->
  i < Zlength l ->
  Znth i l 0 <> 97 -> Znth i l 0 <> 101 -> Znth i l 0 <> 105 ->
  Znth i l 0 <> 111 -> Znth i l 0 <> 117 ->
  Znth i l 0 <> 65 -> Znth i l 0 <> 69 -> Znth i l 0 <> 73 ->
  Znth i l 0 <> 79 -> Znth i l 0 <> 85 ->
  count_regular_vowels_upto (i + 1) l =
  count_regular_vowels_upto i l.
Proof.
  intros i l Hi Hlt H97 H101 H105 H111 H117 H65 H69 H73 H79 H85.
  unfold count_regular_vowels_upto.
  rewrite firstn_succ_Znth_64 by lia.
  rewrite count_regular_vowels_list_app.
  simpl.
  rewrite is_regular_vowel_false by auto.
  simpl. lia.
Qed.

Lemma last_y_add_zero : forall l,
  Zlength l = 0 ->
  last_y_add l = 0.
Proof.
  intros l Hlen.
  unfold last_y_add.
  rewrite Hlen, Z.eqb_refl.
  reflexivity.
Qed.

Lemma last_y_add_hit : forall l n,
  Zlength l = n ->
  n > 0 ->
  (Znth (n - 1) l 0 = 121 \/ Znth (n - 1) l 0 = 89) ->
  last_y_add l = 1.
Proof.
  intros l n Hlen Hpos Hy.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y.
  destruct Hy as [Hy | Hy]; rewrite Hy.
  - rewrite Z.eqb_refl. reflexivity.
  - replace (Z.eqb 89 121) with false by reflexivity.
    rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma last_y_add_miss : forall l n,
  Zlength l = n ->
  n > 0 ->
  Znth (n - 1) l 0 <> 121 ->
  Znth (n - 1) l 0 <> 89 ->
  last_y_add l = 0.
Proof.
  intros l n Hlen Hpos H121 H89.
  unfold last_y_add.
  rewrite Hlen.
  replace (Z.eqb n 0) with false by (symmetry; apply Z.eqb_neq; lia).
  unfold is_y.
  replace (Z.eqb (Znth (n - 1) l 0) 121) with false by
    (symmetry; apply Z.eqb_neq; lia).
  replace (Z.eqb (Znth (n - 1) l 0) 89) with false by
    (symmetry; apply Z.eqb_neq; lia).
  reflexivity.
Qed.

Lemma problem_64_spec_intro : forall s output,
  output = count_regular_vowels_upto (Zlength s) s + last_y_add s ->
  problem_64_spec s output.
Proof.
  intros s output Hout.
  unfold problem_64_spec, count_regular_vowels_upto in *.
  assert (Hn : Z.to_nat (Zlength s) = length s) by (rewrite Zlength_correct; lia).
  rewrite Hn in Hout.
  rewrite firstn_all in Hout.
  exact Hout.
Qed.
