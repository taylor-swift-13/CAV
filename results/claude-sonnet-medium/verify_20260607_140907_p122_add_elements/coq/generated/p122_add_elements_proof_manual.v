Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_140907_p122_add_elements Require Import p122_add_elements_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p122_add_elements.

(* Helper lemmas -- placed before Local Open Scope sac to avoid sac-scope notation conflicts *)

Lemma two_digit_bool_equiv : forall x : Z,
  Z.leb (-99) x && Z.leb x 99 = is_at_most_two_digits x.
Proof.
  intro x. unfold is_at_most_two_digits.
  case_eq (Z.leb (-99) x); case_eq (Z.leb x 99);
  case_eq (Z.ltb (-100) x); case_eq (Z.ltb x 100);
  intros H1 H2 H3 H4; try reflexivity;
  rewrite ?Z.leb_le, ?Z.leb_nle, ?Z.ltb_lt, ?Z.ltb_ge in *; lia.
Qed.

Lemma sum_two_digit_upto_step : forall (i : Z) (l : list Z),
  0 <= i ->
  sum_two_digit_upto (i + 1) l =
  if Z.leb (-99) (Znth i l 0) && Z.leb (Znth i l 0) 99
  then sum_two_digit_upto i l + Znth i l 0
  else sum_two_digit_upto i l.
Proof.
  intros i l Hi.
  unfold sum_two_digit_upto.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  2: { replace (i + 1) with (Z.succ i) by lia.
       rewrite Z2Nat.inj_succ by lia. reflexivity. }
  simpl (sum_two_digit_upto_nat (S (Z.to_nat i)) l).
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

(* Prove with Z.leb form directly to avoid rewriting under filter binders *)
Lemma sum_two_digit_upto_nat_eq_fold_leb : forall (n : nat) (l : list Z),
  sum_two_digit_upto_nat n l =
  fold_left Z.add (filter (fun x => Z.leb (-99) x && Z.leb x 99) (firstn n l)) 0.
Proof.
  induction n; intros l.
  - simpl. reflexivity.
  - simpl (sum_two_digit_upto_nat (S n) l).
    rewrite IHn.
    destruct (le_lt_dec (length l) n) as [Hge | Hlt].
    + assert (Hf1: firstn n l = l) by (apply firstn_all2; lia).
      assert (Hf2: firstn (S n) l = l) by (apply firstn_all2; lia).
      assert (Hz : Znth (Z.of_nat n) l 0 = 0).
      { unfold Znth.
        destruct (Z_lt_dec (Z.of_nat n) 0) as [Hn | Hn]. { lia. }
        rewrite Nat2Z.id.
        apply nth_overflow. lia. }
      rewrite Hf1, Hf2, Hz.
      destruct (Z.leb (-99) 0 && Z.leb 0 99); ring.
    + assert (Hznth : Znth (Z.of_nat n) l 0 = nth n l 0).
      { unfold Znth.
        destruct (Z_lt_dec (Z.of_nat n) 0) as [Hn | Hn]. { lia. }
        rewrite Nat2Z.id. reflexivity. }
      rewrite Hznth.
      assert (Hfirstn : firstn (S n) l = firstn n l ++ (nth n l 0 :: nil)).
      { clear - Hlt.
        revert n Hlt.
        induction l as [|a t IH]; intros n Hlt.
        - simpl in Hlt. lia.
        - destruct n as [|n'].
          + simpl. reflexivity.
          + simpl. f_equal. apply IH. simpl in Hlt. lia. }
      rewrite Hfirstn.
      rewrite filter_app.
      rewrite fold_left_app.
      simpl (filter (fun x => Z.leb (-99) x && Z.leb x 99) (nth n l 0 :: nil)).
      destruct (Z.leb (-99) (nth n l 0) && Z.leb (nth n l 0) 99) eqn:Hc.
      * simpl. ring.
      * simpl. reflexivity.
Qed.

Lemma sum_two_digit_upto_nat_eq_fold : forall (n : nat) (l : list Z),
  sum_two_digit_upto_nat n l =
  fold_left Z.add (filter is_at_most_two_digits (firstn n l)) 0.
Proof.
  intros n l.
  rewrite sum_two_digit_upto_nat_eq_fold_leb.
  f_equal.
  apply filter_ext.
  intro x. apply two_digit_bool_equiv.
Qed.

Lemma sum_two_digit_upto_eq_fold : forall (k : Z) (l : list Z),
  0 <= k ->
  sum_two_digit_upto k l =
  fold_left Z.add (filter is_at_most_two_digits (sublist 0 k l)) 0.
Proof.
  intros k l Hk.
  unfold sum_two_digit_upto, sublist.
  simpl (Z.to_nat 0).
  simpl (skipn 0 (firstn (Z.to_nat k) l)).
  apply sum_two_digit_upto_nat_eq_fold.
Qed.

Local Open Scope sac.

Lemma proof_of_p122_add_elements_safety_wit_6 : p122_add_elements_safety_wit_6.
Proof.
  pre_process.
  split_pures; dump_pre_spatial;
  match goal with
  | Hrange : sum_two_digit_int_range ?kp ?lv2,
    Hi : 0 <= ?ii, Hlt : ?ii < ?kp,
    Hs : ?ss = sum_two_digit_upto ?ii ?lv2 |- _ =>
    pose proof (Hrange ii Hi Hlt) as [[? ?] [Hmin Hmax]]; rewrite Hs; lia
  end.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_1 : p122_add_elements_entail_wit_1.
Proof.
  pre_process.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_1 : p122_add_elements_entail_wit_2_1.
Proof.
  pre_process.
  entailer!.
  all: try lia.
  all: try assumption.
  (* remaining: s + Znth i lv 0 = sum_two_digit_upto (i+1) lv *)
  rewrite sum_two_digit_upto_step by lia.
  (* assert each leb separately to avoid sac-scope && conflict *)
  assert (Hle1: Z.leb (-99) (Znth i lv 0) = true) by (apply Z.leb_le; lia).
  assert (Hle2: Z.leb (Znth i lv 0) 99 = true) by (apply Z.leb_le; lia).
  rewrite Hle1, Hle2. simpl. lia.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_2 : p122_add_elements_entail_wit_2_2.
Proof.
  pre_process.
  entailer!.
  all: try lia.
  all: try assumption.
  (* remaining: s = sum_two_digit_upto (i+1) lv *)
  rewrite sum_two_digit_upto_step by lia.
  assert (Hle: Z.leb (-99) (Znth i lv 0) = false)
    by (rewrite <- Bool.not_true_iff_false; rewrite Z.leb_le; lia).
  rewrite Hle. simpl. lia.
Qed.

Lemma proof_of_p122_add_elements_entail_wit_2_3 : p122_add_elements_entail_wit_2_3.
Proof.
  pre_process.
  entailer!.
  all: try lia.
  all: try assumption.
  (* remaining: s = sum_two_digit_upto (i+1) lv *)
  rewrite sum_two_digit_upto_step by lia.
  assert (Hle: Z.leb (Znth i lv 0) 99 = false)
    by (rewrite <- Bool.not_true_iff_false; rewrite Z.leb_le; lia).
  rewrite Hle, Bool.andb_false_r. simpl. lia.
Qed.

Lemma proof_of_p122_add_elements_return_wit_1 : p122_add_elements_return_wit_1.
Proof.
  pre_process.
  assert (Heq : i = k_pre) by lia.
  subst i.
  entailer!.
  all: try lia.
  all: try assumption.
  (* remaining: problem_122_spec lv k_pre s *)
  unfold problem_122_spec.
  rewrite <- sum_two_digit_upto_eq_fold by lia.
  assumption.
Qed.
