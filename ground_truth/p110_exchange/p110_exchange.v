(* spec/110 *)
(*
In this problem, you will implement a function that takes two lists of numbers,
and determines whether it is possible to perform an exchange of elements
between them to make lst1 a list of only even numbers.
There is no limit on the number of exchanged elements between lst1 and lst2.
If it is possible to exchange elements between the lst1 and lst2 to make
all the elements of lst1 to be even, return "YES".
Otherwise, return "NO".
For example:
exchange([1, 2, 3, 4], [1, 2, 3, 4]) => "YES"
exchange([1, 2, 3, 4], [1, 5, 3, 4]) => "NO"
It is assumed that the input lists will be non-empty.
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 两个输入列表均非空 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_110 (z : Z) : string :=
  if Z.eqb z 1 then "YES" else "NO".

Definition nonnegative_list (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition problem_110_pre (lst1 lst2 : list Z) : Prop :=
  lst1 <> [] /\ lst2 <> [].

Definition even_zb (x : Z) : bool :=
  Z.eqb (Z.rem x 2) 0.

Fixpoint count_even_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if even_zb x then 1 else 0) + count_even_list xs
  end.

Definition count_even_upto (i : Z) (l : list Z) : Z :=
  count_even_list (sublist 0 i l).

Definition problem_110_spec (lst1 lst2 : list Z) (output : Z) : Prop :=
  let odds_in_lst1 := Zlength lst1 - count_even_list lst1 in
  let evens_in_lst2 := count_even_list lst2 in
  if Z.leb odds_in_lst1 evens_in_lst2
  then yesno_of_110 output = "YES"%string
  else yesno_of_110 output = "NO"%string.

Lemma count_even_list_nonneg : forall l,
  0 <= count_even_list l.
Proof.
  induction l; simpl; try lia.
  destruct (even_zb a); lia.
Qed.

Lemma count_even_list_le_len : forall l,
  count_even_list l <= Zlength l.
Proof.
  induction l; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (even_zb a); lia.
Qed.

Lemma count_even_list_app_single : forall l x,
  count_even_list (l ++ [x]) =
  count_even_list l + if even_zb x then 1 else 0.
Proof.
  induction l as [| y ys IH]; intros x; simpl.
  - lia.
  - rewrite IH.
    destruct (even_zb y); destruct (even_zb x); lia.
Qed.

Lemma count_even_upto_bounds : forall i l,
  0 <= i <= Zlength l ->
  0 <= count_even_upto i l <= i.
Proof.
  intros i l Hi.
  unfold count_even_upto.
  split.
  - apply count_even_list_nonneg.
  - pose proof (count_even_list_le_len (sublist 0 i l)).
    rewrite Zlength_sublist in H by lia.
    lia.
Qed.

Lemma count_even_upto_0 : forall l,
  count_even_upto 0 l = 0.
Proof.
  intros l.
  unfold count_even_upto, sublist.
  simpl.
  reflexivity.
Qed.

Lemma count_even_upto_full : forall l n,
  n = Zlength l ->
  count_even_upto n l = count_even_list l.
Proof.
  intros l n Hn.
  subst n.
  unfold count_even_upto.
  rewrite sublist_self by reflexivity.
  reflexivity.
Qed.

Lemma count_even_upto_step_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = true ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - rewrite count_even_list_app_single.
    rewrite Heven.
    lia.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma count_even_upto_step_not_even : forall i l,
  0 <= i < Zlength l ->
  even_zb (Znth i l 0) = false ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros i l Hi Heven.
  unfold count_even_upto.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  replace (sublist i (i + 1) l) with (Znth i l 0 :: nil).
  - rewrite count_even_list_app_single.
    rewrite Heven.
    lia.
  - symmetry. apply sublist_single. lia.
Qed.

Lemma even_zb_rem_true : forall x,
  Z.rem x 2 = 0 ->
  even_zb x = true.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_eq.
  exact H.
Qed.

Lemma even_zb_rem_false : forall x,
  Z.rem x 2 <> 0 ->
  even_zb x = false.
Proof.
  intros x H.
  unfold even_zb.
  apply Z.eqb_neq.
  exact H.
Qed.

Lemma count_even_upto_step_rem_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 = 0 ->
  count_even_upto (i + 1) l = count_even_upto i l + 1.
Proof.
  intros.
  apply count_even_upto_step_even; auto.
  apply even_zb_rem_true; assumption.
Qed.

Lemma count_even_upto_step_rem_not_even : forall i l,
  0 <= i < Zlength l ->
  Z.rem (Znth i l 0) 2 <> 0 ->
  count_even_upto (i + 1) l = count_even_upto i l.
Proof.
  intros.
  apply count_even_upto_step_not_even; auto.
  apply even_zb_rem_false; assumption.
Qed.

Lemma problem_110_spec_true : forall lst1 lst2 total_even,
  problem_110_pre lst1 lst2 ->
  nonnegative_list lst1 ->
  nonnegative_list lst2 ->
  total_even = count_even_list lst1 + count_even_list lst2 ->
  Zlength lst1 <= total_even ->
  problem_110_spec lst1 lst2 1.
Proof.
  intros lst1 lst2 total_even _ _ _ Htotal Hcmp.
  unfold problem_110_spec, yesno_of_110.
  replace (Z.eqb 1 1) with true by reflexivity.
  assert ((Z.leb (Zlength lst1 - count_even_list lst1) (count_even_list lst2)) = true).
  { apply Z.leb_le. lia. }
  rewrite H.
  reflexivity.
Qed.

Lemma problem_110_spec_false : forall lst1 lst2 total_even,
  problem_110_pre lst1 lst2 ->
  nonnegative_list lst1 ->
  nonnegative_list lst2 ->
  total_even = count_even_list lst1 + count_even_list lst2 ->
  total_even < Zlength lst1 ->
  problem_110_spec lst1 lst2 0.
Proof.
  intros lst1 lst2 total_even _ _ _ Htotal Hcmp.
  unfold problem_110_spec, yesno_of_110.
  replace (Z.eqb 0 1) with false by reflexivity.
  assert ((Z.leb (Zlength lst1 - count_even_list lst1) (count_even_list lst2)) = false).
  { apply Z.leb_gt. lia. }
  rewrite H.
  reflexivity.
Qed.
