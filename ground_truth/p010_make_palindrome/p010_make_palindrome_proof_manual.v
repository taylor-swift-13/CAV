Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p010_make_palindrome Require Import p010_make_palindrome_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Import naive_C_Rules.
Require Import p010_make_palindrome.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p010_make_palindrome.v so public contract files expose definitions only. *)

Lemma pal_suffix_empty_10 : forall input,
  Zlength input = 0 ->
  pal_suffix 0 input.
Proof.
  intros input Hlen.
  unfold pal_suffix.
  split; [lia |].
  intros k Hk _.
  lia.
Qed.
Lemma pal_suffix_last_10 : forall input,
  0 < Zlength input ->
  pal_suffix (Zlength input - 1) input.
Proof.
  intros input Hlen.
  unfold pal_suffix.
  split; [lia |].
  intros k Hk Hmirror.
  lia.
Qed.
Lemma ascii_of_inj_range_10 : forall a b,
  0 <= a < 256 ->
  0 <= b < 256 ->
  ascii_of a = ascii_of b ->
  a = b.
Proof.
  intros a b Ha Hb Heq.
  apply (f_equal nat_of_ascii) in Heq.
  unfold ascii_of in Heq.
  repeat rewrite nat_ascii_embedding in Heq by lia.
  lia.
Qed.
Lemma first_pal_suffix_empty_10 : forall input,
  Zlength input = 0 ->
  first_pal_suffix 0 input.
Proof.
  intros input Hlen.
  unfold first_pal_suffix.
  split; [lia |].
  split.
  - apply pal_suffix_empty_10; assumption.
  - intros t Ht.
    lia.
Qed.
Lemma Zlength_rev_10 : forall {A : Type} (l : list A),
  Zlength (rev l) = Zlength l.
Proof.
  intros A l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.
Lemma Znth_rev_10 : forall {A : Type} (l : list A) i d,
  0 <= i < Zlength l ->
  Znth i (rev l) d = Znth (Zlength l - 1 - i) l d.
Proof.
  intros A l i d Hi.
  unfold Znth.
  rewrite rev_nth by (rewrite Zlength_correct in Hi; lia).
  replace (Datatypes.length l - S (Z.to_nat i))%nat
    with (Z.to_nat (Zlength l - 1 - i)).
  - reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.
Lemma Znth_firstn_10 : forall {A : Type} n (l : list A) i d,
  0 <= i ->
  i < Z.of_nat n ->
  Znth i (firstn n l) d = Znth i l d.
Proof.
  intros A n l i d Hi Hlt.
  unfold Znth.
  rewrite List.nth_firstn.
  destruct (Z.to_nat i <? n)%nat eqn:Hcmp.
  - reflexivity.
  - apply Nat.ltb_ge in Hcmp.
    lia.
Qed.
Lemma Zlength_make_pal_output_10 : forall best input,
  0 <= best <= Zlength input ->
  Zlength (make_pal_output best input) = Zlength input + best.
Proof.
  intros best input Hbest.
  unfold make_pal_output.
  rewrite Zlength_app.
  rewrite Zlength_rev_10.
  rewrite !Zlength_correct.
  rewrite firstn_length.
  rewrite Zlength_correct in Hbest.
  replace (Init.Nat.min (Z.to_nat best) (Datatypes.length input))
    with (Z.to_nat best) by lia.
  lia.
Qed.
Lemma make_pal_output_prefix_10 : forall best input k,
  0 <= best <= Zlength input ->
  0 <= k < Zlength input ->
  Znth k (make_pal_output best input) 0 = Znth k input 0.
Proof.
  intros best input k Hbest Hk.
  unfold make_pal_output.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.
Lemma make_pal_output_suffix_10 : forall best input k,
  0 <= best <= Zlength input ->
  0 <= k < best ->
  Znth (Zlength input + k) (make_pal_output best input) 0 =
  Znth (best - 1 - k) input 0.
Proof.
  intros best input k Hbest Hk.
  unfold make_pal_output.
  rewrite app_Znth2 by lia.
  rewrite Zlength_correct.
  replace (Zlength input + k - Z.of_nat (Datatypes.length input)) with k
    by (rewrite Zlength_correct; lia).
  assert (Hfirst_len : Zlength (firstn (Z.to_nat best) input) = best).
  {
    rewrite Zlength_correct, firstn_length.
    replace (Init.Nat.min (Z.to_nat best) (Datatypes.length input))
      with (Z.to_nat best) by (rewrite Zlength_correct in Hbest; lia).
    lia.
  }
  rewrite Znth_rev_10 by (rewrite Hfirst_len; lia).
  rewrite Hfirst_len.
  rewrite Znth_firstn_10 by lia.
  replace (Z.of_nat (Datatypes.length input) + k -
    Z.of_nat (Datatypes.length input)) with k by lia.
  reflexivity.
Qed.
Lemma Zlength_map_10 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros A B f l.
  repeat rewrite Zlength_correct.
  rewrite map_length.
  reflexivity.
Qed.
Lemma Znth_map_10 : forall {A B : Type} (f : A -> B) l i da db,
  0 <= i < Zlength l ->
  Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  unfold Znth.
  transitivity (nth (Z.to_nat i) (map f l) (f da)).
  - apply nth_indep.
    rewrite map_length.
    rewrite Zlength_correct in Hi.
    lia.
  - apply map_nth.
Qed.
Lemma string_of_list_app_10 : forall a b,
  string_of_list (a ++ b) =
  String.append (string_of_list a) (string_of_list b).
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_length_append_nat_10 : forall a b,
  String.length (String.append a b) =
  (String.length a + String.length b)%nat.
Proof.
  induction a as [| c rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_length_append_z_10 : forall a b,
  Z.of_nat (String.length (String.append a b)) =
  Z.of_nat (String.length a) + Z.of_nat (String.length b).
Proof.
  intros a b.
  rewrite string_length_append_nat_10.
  lia.
Qed.
Lemma string_of_list_as_ascii_10 : forall l,
  string_of_list l = string_of_list_ascii (map ascii_of l).
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma list_ascii_of_string_string_of_list : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [| x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_of_list_rev_10 : forall l,
  string_of_list_ascii (rev (list_ascii_of_string (string_of_list l))) =
  string_of_list (rev l).
Proof.
  intros l.
  rewrite list_ascii_of_string_string_of_list.
  rewrite <- map_rev.
  rewrite string_of_list_as_ascii_10.
  reflexivity.
Qed.
Lemma list_ascii_of_string_app_10 : forall a b,
  list_ascii_of_string (String.append a b) =
  list_ascii_of_string a ++ list_ascii_of_string b.
Proof.
  induction a as [| c rest IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_of_list_ascii_list_ascii_of_string_10 : forall s,
  string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  induction s as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma list_ascii_of_string_string_of_list_ascii_10 : forall l,
  list_ascii_of_string (string_of_list_ascii l) = l.
Proof.
  induction l as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma Zlength_list_ascii_of_string_10 : forall s,
  Zlength (list_ascii_of_string s) = Z.of_nat (String.length s).
Proof.
  induction s as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma prefix_append_true_10 : forall s t,
  prefix s (String.append s t) = true.
Proof.
  induction s as [| c rest IH]; intros t; simpl.
  - destruct t; reflexivity.
  - destruct (ascii_dec c c) as [_ | Hneq].
    + apply IH.
    + contradiction.
Qed.
Lemma prefix_true_exists_suffix_10 : forall s p,
  prefix s p = true ->
  exists q, p = String.append s q.
Proof.
  induction s as [| c rest IH]; intros p Hprefix.
  - exists p. reflexivity.
  - destruct p as [| d prest]; simpl in Hprefix; try discriminate.
    destruct (ascii_dec c d) as [Heq | Hneq]; try discriminate.
    subst d.
    destruct (IH prest Hprefix) as [q ->].
    exists q. reflexivity.
Qed.
Lemma Zlength_skipn_10 : forall n (l : list Z),
  0 <= n <= Zlength l ->
  Zlength (skipn (Z.to_nat n) l) = Zlength l - n.
Proof.
  intros n l Hn.
  rewrite !Zlength_correct.
  rewrite skipn_length.
  replace (Datatypes.length l - Z.to_nat n)%nat
    with (Z.to_nat (Z.of_nat (Datatypes.length l) - n)) by lia.
  rewrite Z2Nat.id by (rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.
Lemma Znth_skipn_10 : forall n i (l : list Z) d,
  0 <= n <= Zlength l ->
  0 <= i < Zlength l - n ->
  Znth i (skipn (Z.to_nat n) l) d = Znth (n + i) l d.
Proof.
  intros n i l d Hn Hi.
  unfold Znth.
  rewrite nth_skipn.
  replace (Z.to_nat n + Z.to_nat i)%nat with (Z.to_nat (n + i)) by lia.
  reflexivity.
Qed.
Lemma pal_suffix_skipn_rev_10 : forall best input,
  pal_suffix best input ->
  skipn (Z.to_nat best) input = rev (skipn (Z.to_nat best) input).
Proof.
  intros best input [Hbest Hpal].
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Zlength_rev_10. reflexivity.
  - intros i Hi.
    rewrite Znth_rev_10 by lia.
    rewrite Zlength_skipn_10 by lia.
    rewrite Zlength_skipn_10 in Hi by lia.
    rewrite (Znth_skipn_10 best i input 0) by lia.
    rewrite (Znth_skipn_10 best (Zlength input - best - 1 - i) input 0) by lia.
    replace (best + (Zlength input - best - 1 - i))
      with (Zlength input - 1 - i) by lia.
    destruct (Z_lt_ge_dec i (Zlength input - best - 1 - i)) as [Hmirror | Hmirror].
    + apply Hpal; lia.
    + destruct (Z.eq_dec i (Zlength input - best - 1 - i)) as [Heq | Hneq].
      * replace (Zlength input - 1 - i) with (best + i) by lia.
        reflexivity.
      * symmetry.
        replace (best + i) with
          (Zlength input - 1 - (Zlength input - best - 1 - i)) by lia.
        replace (Zlength input - 1 - i) with
          (best + (Zlength input - best - 1 - i)) by lia.
        apply Hpal; lia.
Qed.
Lemma make_pal_output_palindrome_list_10 : forall best input,
  first_pal_suffix best input ->
  make_pal_output best input = rev (make_pal_output best input).
Proof.
  intros best input [Hbest [Hpal Hmin]].
  unfold make_pal_output.
  set (pre := firstn (Z.to_nat best) input).
  set (suf := skipn (Z.to_nat best) input).
  assert (Hsplit : input = pre ++ suf).
  { subst pre suf. rewrite firstn_skipn. reflexivity. }
  assert (Hsuf : suf = rev suf).
  { subst suf. apply pal_suffix_skipn_rev_10. exact Hpal. }
  rewrite Hsplit.
  rewrite rev_app_distr.
  rewrite rev_app_distr.
  rewrite rev_involutive.
  rewrite <- Hsuf.
  repeat rewrite <- app_assoc.
  reflexivity.
Qed.
Lemma make_pal_output_ext_10 : forall len input best out_l,
  Zlength input = len ->
  0 <= best <= len ->
  Zlength out_l = len + best ->
  (forall p, 0 <= p < len -> Znth p out_l 0 = Znth p input 0) ->
  (forall p, 0 <= p < best ->
    Znth (len + p) out_l 0 = Znth (best - 1 - p) input 0) ->
  out_l = make_pal_output best input.
Proof.
  intros len input best out_l Hlen Hbest Hout_len Hprefix Hsuffix.
  apply (proj2 (list_eq_ext _ _ 0)).
  split.
  - rewrite Hout_len.
    rewrite Zlength_make_pal_output_10; lia.
  - intros i Hi.
    rewrite Hout_len in Hi.
    destruct (Z_lt_ge_dec i len) as [Hlt | Hge].
    + rewrite Hprefix by lia.
      symmetry.
      rewrite make_pal_output_prefix_10 by lia.
      reflexivity.
    + replace i with (len + (i - len)) by lia.
      rewrite Hsuffix by lia.
      symmetry.
      rewrite <- Hlen.
      rewrite make_pal_output_suffix_10 by lia.
      reflexivity.
Qed.
Lemma prefix_palindrome_implies_pal_suffix_10 : forall input q t,
  ascii_range input ->
  t = Z.of_nat (String.length q) ->
  t <= Zlength input ->
  palindrome (String.append (string_of_list input) q) ->
  pal_suffix t input.
Proof.
  intros input q t Hrange Ht Ht_bound Hpal.
  unfold palindrome in Hpal.
  set (p := String.append (string_of_list input) q) in *.
  assert (Hpal_list :
    list_ascii_of_string p = rev (list_ascii_of_string p)).
  {
    rewrite Hpal at 1.
    apply list_ascii_of_string_string_of_list_ascii_10.
  }
  unfold pal_suffix.
  split; [lia |].
  intros k Hk Hmirror.
  assert (HP :
    list_ascii_of_string p =
    map ascii_of input ++ list_ascii_of_string q).
  {
    subst p.
    rewrite list_ascii_of_string_app_10.
    rewrite list_ascii_of_string_string_of_list.
    reflexivity.
  }
  assert (Hidx :
    Znth (t + k) (list_ascii_of_string p) " "%char =
    Znth (Zlength (list_ascii_of_string p) - 1 - (t + k))
      (list_ascii_of_string p) " "%char).
  {
    rewrite Hpal_list at 1.
    rewrite Znth_rev_10.
    - reflexivity.
    - rewrite HP, Zlength_app, Zlength_map_10.
      rewrite Zlength_list_ascii_of_string_10.
      rewrite <- Ht.
      lia.
  }
  rewrite HP in Hidx.
  rewrite Zlength_app, Zlength_map_10 in Hidx.
  rewrite Zlength_list_ascii_of_string_10 in Hidx.
  rewrite <- Ht in Hidx.
  replace (Zlength (map ascii_of input ++ list_ascii_of_string q) - 1 - (t + k))
    with (Zlength input - 1 - k) in Hidx.
  2:{
    rewrite Zlength_app, Zlength_map_10.
    rewrite Zlength_list_ascii_of_string_10.
    rewrite <- Ht.
    lia.
  }
  rewrite app_Znth1 in Hidx by (rewrite Zlength_map_10; lia).
  rewrite app_Znth1 in Hidx by (rewrite Zlength_map_10; lia).
  rewrite (@Znth_map_10 Z ascii ascii_of input (t + k) 0 " "%char) in Hidx by lia.
  replace (Zlength input + t - 1 - (t + k)) with (Zlength input - 1 - k) in Hidx by lia.
  rewrite (@Znth_map_10 Z ascii ascii_of input (Zlength input - 1 - k) 0 " "%char) in Hidx by lia.
  apply ascii_of_inj_range_10; try apply Hrange; try lia.
  exact Hidx.
Qed.
Lemma problem_10_spec_make_pal_output_10 : forall input best,
  ascii_range input ->
  first_pal_suffix best input ->
  problem_10_spec input (make_pal_output best input).
Proof.
  intros input best Hrange Hfirst.
  destruct Hfirst as [Hbest [Hpal Hmin]].
  unfold problem_10_spec, problem_10_spec.
  split.
  - unfold make_pal_output.
    rewrite string_of_list_app_10.
    apply prefix_append_true_10.
  - split.
    + unfold palindrome.
    rewrite string_of_list_rev_10.
    f_equal.
    apply make_pal_output_palindrome_list_10.
    unfold first_pal_suffix.
    exact (conj Hbest (conj Hpal Hmin)).
    + intros p [Hpref Hp_pal].
    destruct (prefix_true_exists_suffix_10 _ _ Hpref) as [q ->].
    rewrite Zlength_make_pal_output_10 by lia.
    rewrite list_ascii_of_string_app_10.
    rewrite Zlength_app.
    rewrite list_ascii_of_string_string_of_list.
    rewrite Zlength_map_10.
    rewrite Zlength_list_ascii_of_string_10.
    assert (Hbest_le_q : best <= Z.of_nat (String.length q)).
    {
      destruct (Z_le_gt_dec (Z.of_nat (String.length q)) (Zlength input))
        as [Hq_bound | Hq_big]; [| lia].
      destruct (Z_lt_ge_dec (Z.of_nat (String.length q)) best) as [Hlt | Hge]; [| lia].
      exfalso.
      apply (Hmin (Z.of_nat (String.length q))); [lia |].
      eapply prefix_palindrome_implies_pal_suffix_10; eauto.
    }
    lia.
Qed.


Lemma proof_of_is_pal_suffix_entail_wit_2 : is_pal_suffix_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  intros k Hk.
  destruct (Z_lt_ge_dec k (i - start_pre)).
  - match goal with
    | Hprefix : forall k_2 : Z,
        0 <= k_2 < i - start_pre ->
        Znth (start_pre + k_2) l 0 = Znth (n_pre - 1 - k_2) l 0 |- _ =>
        apply Hprefix; lia
    end.
  - assert (k = i - start_pre) by lia.
    subst k.
    match goal with
    | Heq : Znth i (app l (cons 0 nil)) 0 =
            Znth j (app l (cons 0 nil)) 0 |- _ =>
        rewrite app_Znth1 in Heq by lia;
        rewrite app_Znth1 in Heq by lia;
        replace (start_pre + (i - start_pre)) with i by lia;
        replace (n_pre - 1 - (i - start_pre)) with j by lia;
        exact Heq
    end.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_1 : is_pal_suffix_return_wit_1.
Proof.
  pre_process.
  Left.
  entailer!.
  unfold pal_suffix, pal_suffix.
  split.
  - lia.
  - intros k Hk Hmirror.
    match goal with
    | Hlen : Zlength l = n_pre |- _ => rewrite Hlen
    end.
    match goal with
    | Hprefix : forall k_2 : Z,
        0 <= k_2 < i - start_pre ->
        Znth (start_pre + k_2) l 0 = Znth (n_pre - 1 - k_2) l 0 |- _ =>
        apply Hprefix; lia
    end.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_2 : is_pal_suffix_return_wit_2.
Proof.
  pre_process.
  Right.
  entailer!.
  unfold pal_suffix, pal_suffix.
  intros [_ Hpal].
  match goal with
  | Hneq : Znth i (app l (cons 0 nil)) 0 <>
           Znth j (app l (cons 0 nil)) 0 |- _ =>
      apply Hneq;
      repeat rewrite app_Znth1 by lia;
      specialize (Hpal (i - start_pre));
      replace (start_pre + (i - start_pre)) with i in Hpal by lia;
      replace (Zlength l - 1 - (i - start_pre)) with j in Hpal by lia;
      apply Hpal; lia
  end.
Qed. 

Lemma proof_of_is_pal_suffix_return_wit_3 : is_pal_suffix_return_wit_3.
Proof.
  pre_process.
  Left.
  entailer!.
  unfold pal_suffix, pal_suffix.
  split.
  - lia.
  - intros k Hk _.
    lia.
Qed. 

Lemma proof_of_p010_make_palindrome_safety_wit_14 : p010_make_palindrome_safety_wit_14.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_p010_make_palindrome_safety_wit_16 : p010_make_palindrome_safety_wit_16.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_p010_make_palindrome_safety_wit_18 : p010_make_palindrome_safety_wit_18.
Proof.
  pre_process.
  entailer!.
  all: change (Z.quot 2147483647 2) with 1073741823 in *; lia.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_2_2 : p010_make_palindrome_entail_wit_2_2.
Proof.
  pre_process.
  Right.
  entailer!.
  intros t Ht Hpal.
  destruct (Z_lt_ge_dec t i) as [Hlt | Hge].
  - match goal with
    | Hnone : forall t_2 : Z, 0 <= t_2 < i -> ~ pal_suffix t_2 l |- _ =>
        apply (Hnone t); [lia | exact Hpal]
    end.
  - assert (t = i) by lia.
    subst t.
    match goal with
    | Hnot : ~ pal_suffix i l |- _ => exact (Hnot Hpal)
    end.
Qed.

Lemma proof_of_p010_make_palindrome_entail_wit_3_1 : p010_make_palindrome_entail_wit_3_1.
Proof.
  pre_process.
  assert (Hlen0 : len = 0).
  {
    destruct (Z_lt_ge_dec 0 len) as [Hpos | Hzero]; [exfalso | lia].
    match goal with
    | Hnone : forall t : Z, 0 <= t /\ t < i -> ~ pal_suffix t l |- _ =>
        apply (Hnone (len - 1)); [lia | idtac]
    end.
    replace (len - 1) with (Zlength l - 1) by lia.
    apply pal_suffix_last_10.
    lia.
  }
  subst len.
  subst best.
  Exists (@nil Z).
  rewrite Hlen0.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 ((0 + 0) + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - rewrite (CharArray.undef_seg_empty retval 0).
    entailer!.
  - apply first_pal_suffix_empty_10.
    lia.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_3_2 : p010_make_palindrome_entail_wit_3_2.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 ((len + best) + 1)).
  2: lia.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - rewrite (CharArray.undef_seg_empty retval 0).
    entailer!.
  - change (Z.quot 2147483647 2) with 1073741823 in *; lia.
  - unfold first_pal_suffix.
    split.
    + lia.
    + split.
      * match goal with
        | Hpal : pal_suffix best l |- _ => exact Hpal
        end.
      * match goal with
        | Hmin : forall t : Z, 0 <= t < best -> ~ pal_suffix t l |- _ => exact Hmin
        end.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_4 : p010_make_palindrome_entail_wit_4.
Proof.
  pre_process.
  Exists (app out_l_2 (cons (Znth i (app l (cons 0 nil)) 0) nil)).
  entailer!.
  - intros p Hp.
    destruct (Z_lt_ge_dec p i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hprefix : forall p : Z, 0 <= p < i -> _ |- _ =>
          apply Hprefix; lia
      end.
    + assert (p = i) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      reflexivity.
  - intros p Hp.
    destruct (Z_lt_ge_dec p i) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hnz : forall p : Z, 0 <= p < i -> Znth p out_l_2 0 <> 0 |- _ =>
          apply Hnz; lia
      end.
    + assert (p = i) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (i - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      match goal with
      | Hnz_l : forall k : Z, 0 <= k < len -> Znth k l 0 <> 0 |- _ =>
          apply Hnz_l; lia
      end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_5 : p010_make_palindrome_entail_wit_5.
Proof.
  pre_process.
  assert (Hi_len : i = len) by lia.
  subst i.
  Exists out_l_2.
  entailer!.
  - replace (len + 0) with (Zlength out_l_2) by lia.
    entailer!.
  - intros p Hp.
    match goal with
    | Hprefix : forall q : Z, 0 <= q < Zlength out_l_2 ->
        Znth q out_l_2 0 = Znth q l 0 |- _ =>
        apply Hprefix; lia
    end.
  - intros p Hp.
    match goal with
    | Hnz : forall q : Z, 0 <= q < Zlength out_l_2 ->
        Znth q out_l_2 0 <> 0 |- _ =>
        apply Hnz; lia
    end.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_6 : p010_make_palindrome_entail_wit_6.
Proof.
  pre_process.
  Exists (app out_l_2 (cons (Znth (best - 1 - k) (app l (cons 0 nil)) 0) nil)).
  entailer!.
  - replace (len + (k + 1)) with (len + k + 1) by lia.
    entailer!.
  - intros p Hp.
    destruct (Z_lt_ge_dec p k) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hsuffix : forall p : Z, 0 <= p < k -> _ |- _ =>
          apply Hsuffix; lia
      end.
    + assert (p = k) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (len + k - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      reflexivity.
  - intros p Hp.
    rewrite app_Znth1 by lia.
    match goal with
    | Hprefix : forall p : Z, 0 <= p < len -> _ |- _ =>
        apply Hprefix; lia
    end.
  - intros p Hp.
    destruct (Z_lt_ge_dec p (len + k)) as [Hlt | Hge].
    + rewrite app_Znth1 by lia.
      match goal with
      | Hnz : forall q : Z, 0 <= q < len + k -> Znth q out_l_2 0 <> 0 |- _ =>
          apply Hnz; lia
      end.
    + assert (p = len + k) by lia.
      subst p.
      rewrite app_Znth2 by lia.
      replace (len + k - Zlength out_l_2) with 0 by lia.
      rewrite Znth0_cons.
      rewrite app_Znth1 by lia.
      match goal with
      | Hnz_l : forall q : Z, 0 <= q < len -> Znth q l 0 <> 0 |- _ =>
          apply Hnz_l; lia
      end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed. 

Lemma proof_of_p010_make_palindrome_entail_wit_7 : p010_make_palindrome_entail_wit_7.
Proof.
  pre_process.
  assert (Hkbest : k = best) by lia.
  subst k.
  assert (Hout_eq : out_l_2 = make_pal_output best l).
  {
    eapply make_pal_output_ext_10; eauto; try lia.
  }
  assert (Hout_len : out_len = len + best) by lia.
  subst out_len.
  Exists (make_pal_output best l).
  entailer!.
  - rewrite <- Hout_eq.
    rewrite (CharArray.undef_seg_empty out (len + best + 1)).
    entailer!.
  - apply problem_10_spec_make_pal_output_10; assumption.
  - intros p Hp.
    rewrite <- Hout_eq in Hp.
    rewrite H19 in Hp.
    rewrite <- Hout_eq.
    match goal with
    | Hnz : forall q : Z, 0 <= q < len + best -> Znth q out_l_2 0 <> 0 |- _ =>
        apply Hnz; lia
    end.
  - rewrite Zlength_make_pal_output_10 by lia. lia.
Qed. 

Lemma proof_of_p010_make_palindrome_return_wit_1 : p010_make_palindrome_return_wit_1.
Proof.
  pre_process.
  Exists out_l_2.
  entailer!.
  - match goal with
    | Hlen : out_len = Zlength out_l_2 |- _ => rewrite Hlen
    end.
    entailer!.
Qed. 

Lemma proof_of_p010_make_palindrome_partial_solve_wit_1_pure : p010_make_palindrome_partial_solve_wit_1_pure.
Proof.
  pre_process.
  entailer!.
  change (Z.quot 2147483647 2) with 1073741823 in *.
  lia.
Qed.

Lemma proof_of_p010_make_palindrome_partial_solve_wit_2_pure : p010_make_palindrome_partial_solve_wit_2_pure.
Proof.
  pre_process.
  entailer!.
  change (Z.quot 2147483647 2) with 1073741823 in *.
  lia.
Qed. 
