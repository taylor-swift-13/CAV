Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p009_rolling_max Require Import p009_rolling_max_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.ZArith.ZArith Lia.
From AUXLib Require Import ListLib.

Import naive_C_Rules.
Require Import p009_rolling_max.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p009_rolling_max.v so public contract files expose definitions only. *)

Lemma rolling_max_f_length : forall m l,
  length (rolling_max_f m l) = length l.
Proof.
  intros m l.
  revert m.
  induction l as [| a l IH]; intros m; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma running_max_val_ge_m : forall m l,
  m <= running_max_val m l.
Proof.
  intros m l.
  revert m.
  induction l as [| a l IH]; intros m; simpl.
  - lia.
  - eapply Z.le_trans.
    + apply Z.le_max_l.
    + apply IH.
Qed.
Lemma running_max_val_ge_nth : forall m l j,
  (j < length l)%nat -> nth j l 0 <= running_max_val m l.
Proof.
  intros m l j Hj.
  revert m j Hj.
  induction l as [| a l IH]; intros m j Hj; simpl in *.
  - lia.
  - destruct j as [| j'].
    + eapply Z.le_trans.
      * apply Z.le_max_r.
      * apply running_max_val_ge_m.
    + apply IH. lia.
Qed.
Lemma running_max_val_source : forall m l,
  running_max_val m l = m \/
  exists j, (j < length l)%nat /\ nth j l 0 = running_max_val m l.
Proof.
  intros m l.
  revert m.
  induction l as [| a l IH]; intros m; simpl.
  - auto.
  - specialize (IH (Z.max m a)).
    destruct IH as [Hkeep | [j [Hj Heq]]].
    + destruct (Z.eq_dec (Z.max m a) m).
      * left. now rewrite Hkeep, e.
      * right. exists 0%nat. split; [simpl; lia|].
        assert (Z.max m a = a) by lia.
        now rewrite Hkeep, H.
    + right. exists (S j). split; [simpl; lia|].
      simpl. exact Heq.
Qed.
Lemma list_int_range_firstn : forall l n,
  list_int_range l -> list_int_range (firstn n l).
Proof.
  intros l n H i Hi.
  assert (Hi_n : (i < n)%nat).
  { rewrite length_firstn in Hi. lia. }
  assert (Hi_l : (i < length l)%nat).
  { rewrite length_firstn in Hi. lia. }
  rewrite nth_firstn by exact Hi_n.
  apply H.
  exact Hi_l.
Qed.
Lemma running_max_val_source_ge : forall m l,
  l <> [] ->
  (forall j, (j < length l)%nat -> m <= nth j l 0) ->
  exists j, (j < length l)%nat /\ nth j l 0 = running_max_val m l.
Proof.
  intros m l Hnn Hall.
  destruct (running_max_val_source m l) as [Hm | Hex].
  - exists 0%nat. split.
    + destruct l; simpl in *; [contradiction|lia].
    + assert (Hmle : m <= nth 0 l 0).
      { apply Hall. destruct l; simpl in *; [contradiction|lia]. }
      assert (Hle : nth 0 l 0 <= running_max_val m l).
      {
        apply (running_max_val_ge_nth m l 0%nat).
        destruct l; simpl in *; [contradiction|lia].
      }
      rewrite Hm in Hle.
      lia.
  - exact Hex.
Qed.
Lemma running_max_val_app : forall m l1 l2,
  running_max_val m (l1 ++ l2) = running_max_val (running_max_val m l1) l2.
Proof.
  intros m l1 l2.
  revert m l2.
  induction l1 as [| a l1 IH]; intros m l2; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma running_max_val_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  running_max_val INT_MIN (sublist 0 (i + 1) l) =
  Z.max (running_max_val INT_MIN (sublist 0 i l)) (Znth i l 0).
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by lia.
  rewrite running_max_val_app.
  simpl. reflexivity.
Qed.
Lemma rolling_max_f_app_single : forall m l x,
  rolling_max_f m (l ++ [x]) =
  rolling_max_f m l ++ [running_max_val m (l ++ [x])].
Proof.
  intros m l x.
  revert m.
  induction l as [| a l IH]; intros m; simpl.
  - reflexivity.
  - rewrite IH.
    change (running_max_val m (a :: l ++ [x])) with
      (running_max_val (Z.max m a) (l ++ [x])).
    reflexivity.
Qed.
Lemma rolling_max_f_sublist_snoc : forall l i,
  0 <= i < Zlength l ->
  rolling_max_f INT_MIN (sublist 0 (i + 1) l) =
  rolling_max_f INT_MIN (sublist 0 i l) ++
  [running_max_val INT_MIN (sublist 0 (i + 1) l)].
Proof.
  intros l i Hi.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by lia.
  apply rolling_max_f_app_single.
Qed.
Lemma nth_rolling_max_f : forall m l i,
  (i < length l)%nat ->
  nth i (rolling_max_f m l) 0 = running_max_val m (firstn (S i) l).
Proof.
  intros m l i Hi.
  revert m i Hi.
  induction l as [| x xs IH]; intros m i Hi; simpl in *.
  - lia.
  - destruct i as [| i'].
    + reflexivity.
    + change (nth i' (rolling_max_f (Z.max m x) xs) 0 =
              running_max_val (Z.max m x) (firstn (S i') xs)).
      apply IH. lia.
Qed.
Lemma problem_9_spec_rolling_max_f : forall l,
  list_int_range l ->
  problem_9_spec l (rolling_max_f INT_MIN l).
Proof.
  intros l Hrange.
  unfold problem_9_spec.
  split.
  - rewrite !Zlength_correct.
    rewrite rolling_max_f_length.
    reflexivity.
  - intros i Hi.
    unfold prefix_max_at.
    rewrite Zlength_correct in Hi.
    set (ni := Z.to_nat i).
    assert (Hi_nat : (ni < length l)%nat).
    {
      unfold ni.
      rewrite <- (rolling_max_f_length INT_MIN l).
      lia.
    }
    change (Znth i (rolling_max_f INT_MIN l) 0) with
      (nth (Z.to_nat i) (rolling_max_f INT_MIN l) 0).
    rewrite nth_rolling_max_f by exact Hi_nat.
    split.
    + intros j Hj.
      unfold Znth.
      assert (Hj_nat : (Z.to_nat j < length (firstn (S ni) l))%nat).
      {
        rewrite length_firstn.
        unfold ni.
        lia.
      }
      assert (Hnth :
        nth (Z.to_nat j) l 0 =
        nth (Z.to_nat j) (firstn (S ni) l) 0)
        by (rewrite Coq.Lists.List.nth_firstn;
            replace (Nat.ltb (Z.to_nat j) (S ni)) with true
              by (symmetry; apply Nat.ltb_lt; unfold ni; lia);
            reflexivity).
      rewrite Hnth.
      apply running_max_val_ge_nth.
      exact Hj_nat.
    + assert (Hpref_nnil : firstn (S ni) l <> []).
      {
        intro Hnil.
        pose proof (f_equal (@length Z) Hnil) as Hlen.
        rewrite length_firstn in Hlen.
        rewrite Nat.min_l in Hlen by lia.
        simpl in Hlen.
        lia.
      }
      assert (Hpref_ge : forall j, (j < length (firstn (S ni) l))%nat ->
        INT_MIN <= nth j (firstn (S ni) l) 0).
      {
        intros j Hj.
        pose proof (list_int_range_firstn l (S ni) Hrange j Hj) as Hjr.
        lia.
      }
      destruct (running_max_val_source_ge INT_MIN (firstn (S ni) l) Hpref_nnil Hpref_ge)
        as [j [Hj Heq]].
      exists (Z.of_nat j).
      split.
      * rewrite length_firstn in Hj.
        unfold ni.
        lia.
      * unfold Znth.
        rewrite Nat2Z.id.
        rewrite Coq.Lists.List.nth_firstn in Heq.
        replace (Nat.ltb j (S ni)) with true in Heq.
        -- exact Heq.
        -- symmetry. apply Nat.ltb_lt.
           rewrite length_firstn in Hj.
           lia.
Qed.


Lemma proof_of_p009_rolling_max_entail_wit_1 : p009_rolling_max_entail_wit_1.
Proof.
	pre_process.
	subst numbers_pre numbers_size_pre out_pre out_size_pre.
	replace (sublist 0 0 lv) with (@nil Z) by reflexivity.
	simpl.
	replace ((- INT_MAX) - 1) with INT_MIN by lia.
	sep_apply (IntArray.undef_full_split_to_undef_seg out0 0 out_size0).
	2: {
		match goal with
		| Hsize : out_size0 = numbers_size0 |- _ => rewrite Hsize
		| Hsize : numbers_size0 = out_size0 |- _ => rewrite <- Hsize
		end;
		lia.
	}
	rewrite (IntArray.undef_seg_empty out0 0).
	rewrite (IntArray.seg_empty out0 0 0).
	entailer!.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_1 : p009_rolling_max_entail_wit_2_1.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : 0 <= i < Zlength lv).
	{
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct, Hlen
		end;
		lia.
	}
	assert (Hnext : running_max_val INT_MIN (sublist 0 (i + 1) lv) = max).
	{
		rewrite running_max_val_sublist_snoc by exact Hi.
		match goal with
		| Hmax : max = running_max_val INT_MIN (sublist 0 i lv) |- _ => rewrite Hmax
		end;
		apply Z.max_l.
		lia.
	}
	rewrite rolling_max_f_sublist_snoc by exact Hi.
	rewrite Hnext.
	entailer!.
Qed.

Lemma proof_of_p009_rolling_max_entail_wit_2_2 : p009_rolling_max_entail_wit_2_2.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : 0 <= i < Zlength lv).
	{
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct, Hlen
		end;
		lia.
	}
	assert (Hnext : running_max_val INT_MIN (sublist 0 (i + 1) lv) = Znth i lv 0).
	{
		rewrite running_max_val_sublist_snoc by exact Hi.
		assert (Hgt : running_max_val INT_MIN (sublist 0 i lv) < Znth i lv 0).
		{
			match goal with
			| Hmax : max = running_max_val INT_MIN (sublist 0 i lv) |- _ => rewrite <- Hmax
			end;
			lia.
		}
		apply Z.max_r.
		lia.
	}
	rewrite rolling_max_f_sublist_snoc by exact Hi.
	rewrite Hnext.
	entailer!.
Qed.

Lemma proof_of_p009_rolling_max_return_wit_1 : p009_rolling_max_return_wit_1.
Proof.
	pre_process.
	prop_apply (IntArray.full_length numbers0 numbers_size0 lv).
	Intros.
	assert (Hi : i = numbers_size0) by lia.
	subst i.
	assert (Hsl : sublist 0 numbers_size0 lv = lv).
	{
		apply sublist_self.
		match goal with
		| Hlen : Z.of_nat (Datatypes.length lv) = numbers_size0 |- _ =>
				rewrite Zlength_correct;
				symmetry;
				exact Hlen
		end.
	}
	rewrite Hsl.
	Exists (rolling_max_f INT_MIN lv).
	match goal with
	| Hsize : out_size0 = numbers_size0 |- _ => rewrite <- Hsize
	| Hsize : numbers_size0 = out_size0 |- _ => rewrite Hsize
	end.
	rewrite (IntArray.undef_seg_empty out0 out_size0).
	sep_apply (IntArray.seg_to_full out0 0 out_size0).
	replace (out0 + 0 * sizeof (INT)) with out0 by lia.
	replace (out_size0 - 0) with out_size0 by lia.
	entailer!.
	apply problem_9_spec_rolling_max_f.
	match goal with
	| Hrange : list_int_range lv |- _ => exact Hrange
	end.
Qed.
