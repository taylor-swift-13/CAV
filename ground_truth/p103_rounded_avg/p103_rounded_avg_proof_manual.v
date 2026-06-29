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
From SimpleC.EE.CAV.ground_truth_p103_rounded_avg Require Import p103_rounded_avg_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import ZArith.
Require Import String.

Import naive_C_Rules.
Require Import p103_rounded_avg.
Require Import base_conversion_lib.
Local Open Scope sac.
Require Import Coq.Strings.Ascii.
Require Import Coq.micromega.Lia.
Require Import Recdef.
From AUXLib Require Import Axioms ListLib.
From SimpleC.SL Require Import IntLib.
Require Import string_bridge base_conversion_lib.

Local Open Scope list_scope.

(* Proof helpers moved from p103_rounded_avg.v so public contract files expose definitions only. *)

Lemma repeat_Z_tail : forall {A: Type} (a: A) n,
  0 <= n ->
  repeat_Z a (n + 1) = repeat_Z a n ++ [a].
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  rewrite <- repeat_cons.
  reflexivity.
Qed.
Lemma Zlength_repeat_Z : forall {A: Type} (a: A) n,
  0 <= n ->
  Zlength (repeat_Z a n) = n.
Proof.
  intros A a n Hn.
  unfold repeat_Z.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.
Lemma base_digits_zero : forall base,
  2 <= base ->
  base_digits 0 base = [48].
Proof.
  intros base Hbase.
  rewrite base_digits_equation.
  replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 0 0) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.
Lemma base_digits_small : forall n base,
  0 < n < base ->
  2 <= base ->
  base_digits n base = [48 + n].
Proof.
  intros n base Hn Hbase.
  rewrite base_digits_equation.
  replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.ltb n base) with true by (symmetry; apply Z.ltb_lt; lia).
  reflexivity.
Qed.
Lemma base_digits_step : forall n base,
  0 < n ->
  2 <= base ->
  base <= n ->
  base_digits n base =
    base_digits (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase Hle.
  rewrite base_digits_equation.
  replace (Z.leb base 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.ltb n base) with false by (symmetry; apply Z.ltb_ge; lia).
  reflexivity.
Qed.
Lemma base_digits_length_pos_le : forall n base,
  0 < n ->
  2 <= base ->
  Zlength (base_digits n base) <= n.
Proof.
  intros n base Hn Hbase.
  functional induction (base_digits n base).
  - lia.
  - apply Z.leb_le in e0. lia.
  - rewrite Zlength_cons, Zlength_nil.
    lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia). lia. }
    pose proof (IHl ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt n base ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma base_digits_nonempty : forall n base,
  base_digits n base <> [].
Proof.
  intros n base.
  functional induction (base_digits n base); simpl; try discriminate.
  intro H.
  apply app_eq_nil in H.
  destruct H as [_ Hnil].
  discriminate Hnil.
Qed.
Lemma base_digits_pos_step : forall n base,
  0 < n ->
  2 <= base ->
  base_digits_pos n base =
    base_digits_pos (n / base) base ++ [48 + n mod base].
Proof.
  intros n base Hn Hbase.
  unfold base_digits_pos at 1.
  replace (Z.leb n 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (Z.ltb_spec n base) as [Hlt | Hge].
  - rewrite base_digits_small by lia.
    unfold base_digits_pos.
    replace (Z.leb (n / base) 0) with true.
    + rewrite app_nil_l. rewrite Z.mod_small by lia. reflexivity.
    + symmetry. apply Z.leb_le.
      rewrite Z.div_small by lia. lia.
  - rewrite base_digits_step by lia.
    unfold base_digits_pos at 1.
    assert (0 < n / base).
    { assert (1 <= n / base) by (apply Z.div_le_lower_bound; lia).
      lia. }
    replace (Z.leb (n / base) 0) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity.
Qed.
Lemma base_count_state_init : forall x base,
  0 < x ->
  base_count_state x base x 0.
Proof.
  intros x base Hx.
  unfold base_count_state.
  lia.
Qed.
Lemma base_count_state_step : forall orig base t digits,
  0 < t ->
  2 <= base ->
  base_count_state orig base t digits ->
  base_count_state orig base (t / base) (digits + 1).
Proof.
  intros orig base t digits Ht Hbase [Ht0 [Hd Hlen]].
  unfold base_count_state.
  split; [apply Z.div_pos; lia | split; [lia |]].
  rewrite (base_digits_pos_step t base) in Hlen by lia.
  rewrite Zlength_app in Hlen.
  change (Zlength [48 + t mod base]) with 1 in Hlen.
  lia.
Qed.
Lemma base_count_state_done : forall orig base digits,
  0 < orig ->
  base_count_state orig base 0 digits ->
  digits = Zlength (base_digits orig base).
Proof.
  intros orig base digits Horig [_ [Hd Hlen]].
  unfold base_digits_pos in Hlen.
  replace (Z.leb 0 0) with true in Hlen by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  change (Zlength (@nil Z)) with 0 in Hlen.
  lia.
Qed.
Lemma base_fill_state_init : forall orig base,
  0 < orig ->
  base_fill_state orig base orig (Zlength (base_digits orig base)) [].
Proof.
  intros orig base Horig.
  unfold base_fill_state, base_digits_pos.
  replace (Z.leb orig 0) with false by (symmetry; apply Z.leb_gt; lia).
  repeat split; try lia.
  - apply Zlength_nonneg.
  - rewrite app_nil_r. reflexivity.
Qed.
Lemma base_fill_state_step : forall orig base x digits suffix,
  0 < x ->
  2 <= base ->
  base_fill_state orig base x digits suffix ->
  base_fill_state orig base (x / base) (digits - 1)
    ((48 + x mod base) :: suffix).
Proof.
  intros orig base x digits suffix Hx Hbase [Hx0 [Hd [Hdigits Hsplit]]].
  unfold base_fill_state.
  rewrite (base_digits_pos_step x base) in Hsplit by lia.
  rewrite (base_digits_pos_step x base) in Hdigits by lia.
  rewrite Zlength_app in Hdigits.
  change (Zlength [48 + x mod base]) with 1 in Hdigits.
  assert (Hdiv_nonneg : 0 <= x / base) by (apply Z.div_pos; lia).
  assert (Hprefix_len : 0 <= Zlength (base_digits_pos (x / base) base))
    by apply Zlength_nonneg.
  split; [exact Hdiv_nonneg | split; [lia | split; [|]]].
  - rewrite Hdigits. lia.
  - rewrite Hsplit.
    rewrite <- app_assoc.
    reflexivity.
Qed.
Lemma base_fill_state_done : forall orig base suffix,
  base_fill_state orig base 0 0 suffix ->
  suffix = base_digits orig base.
Proof.
  intros orig base suffix [_ [_ [_ Hsplit]]].
  unfold base_digits_pos in Hsplit.
  replace (Z.leb 0 0) with true in Hsplit by (symmetry; apply Z.leb_le; lia).
  simpl in Hsplit.
  symmetry. exact Hsplit.
Qed.
Lemma base_fill_full_state_init : forall orig base,
  0 < orig ->
  base_fill_full_state orig base orig
    (Zlength (base_digits orig base))
    (repeat_Z 0 (Zlength (base_digits orig base))).
Proof.
  intros orig base Horig.
  exists [].
  split.
  - apply base_fill_state_init. exact Horig.
  - rewrite app_nil_r. reflexivity.
Qed.
Lemma base_fill_full_state_done : forall orig base out_l,
  base_fill_full_state orig base 0 0 out_l ->
  out_l = base_digits orig base.
Proof.
  intros orig base out_l [suffix [Hstate Hout]].
  pose proof (base_fill_state_done _ _ _ Hstate) as Hsuffix.
  subst suffix.
  rewrite Hout.
  unfold repeat_Z. simpl. reflexivity.
Qed.
Lemma replace_Znth_boundary_app : forall {A: Type} (prefix tail : list A) x y,
  replace_Znth (Zlength prefix) x (prefix ++ y :: tail) =
  prefix ++ x :: tail.
Proof.
  intros A prefix.
  induction prefix as [|a prefix IH]; intros tail x y.
  - reflexivity.
  - rewrite Zlength_cons.
    change (replace_Znth (Z.succ (Zlength prefix)) x
              (a :: (prefix ++ y :: tail)) =
            a :: prefix ++ x :: tail).
    unfold replace_Znth at 1.
    simpl.
    replace (Z.to_nat (Z.succ (Zlength prefix))) with
      (S (Z.to_nat (Zlength prefix))) by (rewrite Zlength_correct; lia).
    simpl.
    fold (@replace_Znth A (Zlength prefix) x (prefix ++ y :: tail)).
    rewrite (IH tail x y).
    reflexivity.
Qed.
Lemma Zlength_replace_Znth_44 : forall {A: Type} (l : list A) n (v : A),
  0 <= n < Zlength l ->
  Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v Hrange.
  revert n Hrange.
  induction l as [|a l IH]; intros n Hrange; simpl.
  - rewrite Zlength_nil in Hrange. lia.
  - unfold replace_Znth in *.
    destruct (Z.to_nat n) eqn:Hn; simpl.
    + repeat rewrite Zlength_cons. reflexivity.
    + repeat rewrite Zlength_cons.
      specialize (IH (Z.of_nat n0)).
      unfold replace_Znth in IH.
      rewrite Nat2Z.id in IH.
      rewrite IH by (rewrite Zlength_cons in Hrange; lia).
      reflexivity.
Qed.
Lemma replace_Znth_repeat_suffix : forall d suffix v,
  0 <= d ->
  replace_Znth d v (repeat_Z 0 (d + 1) ++ suffix) =
  repeat_Z 0 d ++ v :: suffix.
Proof.
  intros d suffix v Hd.
  rewrite repeat_Z_tail by lia.
  rewrite <- app_assoc.
  change ([0] ++ suffix) with (0 :: suffix).
  assert (Hlen : Zlength (repeat_Z 0 d) = d)
    by (rewrite Zlength_repeat_Z; lia).
  rewrite <- Hlen at 1.
  rewrite replace_Znth_boundary_app.
  reflexivity.
Qed.
Lemma base_fill_full_state_step : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  0 <= digits ->
  base < 10 ->
  base_fill_full_state orig base x (digits + 1) out_l ->
  base_fill_full_state orig base (x / base) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod base) 8) out_l).
Proof.
  intros orig base x digits out_l Hx Hbase Hdigits Hbase10
    [suffix [Hstate Hout]].
  exists ((48 + x mod base) :: suffix).
  split.
  - pose proof (base_fill_state_step orig base x (digits + 1) suffix
      Hx Hbase Hstate) as Hstep.
    replace (digits + 1 - 1) with digits in Hstep by lia.
    exact Hstep.
  - rewrite Hout.
    rewrite (signed_last_nbits_eq (48 + x mod base) 8)
      by (pose proof (Z.mod_pos_bound x base ltac:(lia)); lia).
    apply replace_Znth_repeat_suffix. lia.
Qed.
Lemma base_fill_full_state_positive_digits : forall orig base x digits out_l,
  0 < x ->
  2 <= base ->
  base_fill_full_state orig base x digits out_l ->
  1 <= digits.
Proof.
  intros orig base x digits out_l Hx Hbase [suffix [[_ [_ [Hdigits _]]] _]].
  rewrite Hdigits.
  unfold base_digits_pos.
  replace (Z.leb x 0) with false by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits x base) eqn:Hbd.
  - exfalso. apply (base_digits_nonempty x base). exact Hbd.
  - rewrite Zlength_cons.
    pose proof (Zlength_nonneg l). lia.
Qed.
Lemma base_digits_digit_range : forall n base c,
  0 <= n ->
  2 <= base < 10 ->
  In c (base_digits n base) ->
  48 <= c <= 57 /\ c - 48 < base.
Proof.
  intros n base c Hn Hbase.
  functional induction (base_digits n base); intros Hin; simpl in Hin.
  - destruct Hin as [<- | []]; lia.
  - destruct Hin as [<- | []]; lia.
  - destruct Hin as [<- | []].
    apply Z.leb_gt in e0.
    apply Z.ltb_lt in e1.
    change (48 <= 48 + n <= 57 /\ 48 + n - 48 < base).
    lia.
  - apply in_app_or in Hin.
    destruct Hin as [Hin | [<- | []]].
    + apply IHl.
      * apply Z.div_pos; lia.
      * lia.
      * exact Hin.
    + change (48 <= 48 + n mod base <= 57 /\
              48 + n mod base - 48 < base).
      pose proof (Z.mod_pos_bound n base ltac:(lia)).
      lia.
Qed.
Lemma Znth_In_range_103 : forall {A: Type} (l : list A) (d : A) i,
  0 <= i < Zlength l ->
  In (Znth i l d) l.
Proof.
  intros A l d i Hi.
  unfold Znth.
  apply nth_In.
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma binary_digits_nonzero : forall n k,
  0 <= n ->
  0 <= k < Zlength (binary_digits n) ->
  Znth k (binary_digits n) 0 <> 0.
Proof.
  intros n k Hn Hk.
  unfold binary_digits.
  pose proof (base_digits_digit_range n 2 (Znth k (base_digits n 2) 0)
    Hn ltac:(lia) (Znth_In_range_103 (base_digits n 2) 0 k Hk)) as [Hrange _].
  lia.
Qed.
Lemma string_of_list_app : forall a b,
  string_of_list (List.app a b) =
  String.append (string_of_list a) (string_of_list b).
Proof.
  induction a; simpl; intros; congruence.
Qed.
Lemma string_append_assoc : forall a b c : string,
  String.append (String.append a b) c =
  String.append a (String.append b c).
Proof.
  induction a; simpl; intros; congruence.
Qed.
Lemma ascii_of_48 : ascii_of 48 = "0"%char.
Proof. reflexivity. Qed.
Lemma ascii_of_49 : ascii_of 49 = "1"%char.
Proof. reflexivity. Qed.
Lemma ascii_of_45 : ascii_of 45 = "-"%char.
Proof. reflexivity. Qed.
Lemma string_of_list_0 : string_of_list [48] = "0".
Proof. reflexivity. Qed.
Lemma string_of_list_neg1 : string_of_list [45; 49] = "-1".
Proof. reflexivity. Qed.
Lemma zpos_xO_div2 : forall p,
  Z.pos (xO p) / 2 = Z.pos p.
Proof.
  intros p.
  rewrite Pos2Z.inj_xO.
  rewrite Z.mul_comm.
  apply Z.div_mul; lia.
Qed.
Lemma zpos_xO_mod2 : forall p,
  Z.pos (xO p) mod 2 = 0.
Proof.
  intros p.
  rewrite Pos2Z.inj_xO.
  rewrite Z.mul_comm.
  apply Z.mod_mul; lia.
Qed.
Lemma zpos_xI_div2 : forall p,
  Z.pos (xI p) / 2 = Z.pos p.
Proof.
  intros p.
  rewrite Pos2Z.inj_xI.
  replace (2 * Z.pos p + 1) with (Z.pos p * 2 + 1) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.div_small; lia.
Qed.
Lemma zpos_xI_mod2 : forall p,
  Z.pos (xI p) mod 2 = 1.
Proof.
  intros p.
  rewrite Pos2Z.inj_xI.
  replace (2 * Z.pos p + 1) with (Z.pos p * 2 + 1) by lia.
  rewrite Z.add_comm.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.
Lemma base_digits_two_to_binary : forall n,
  0 <= n ->
  string_of_list (base_digits n 2) = to_binary n.
Proof.
  intros n Hn.
  destruct n as [| p | p]; try lia.
  - rewrite base_digits_zero by lia. reflexivity.
  - induction p.
    + rewrite base_digits_step by (try lia; vm_compute; lia).
      rewrite zpos_xI_div2, zpos_xI_mod2.
      rewrite string_of_list_app, IHp by lia.
      simpl.
      rewrite ascii_of_49.
      reflexivity.
    + destruct p.
      * rewrite base_digits_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite string_of_list_app, IHp by lia.
        simpl.
        rewrite ascii_of_48.
        reflexivity.
      * rewrite base_digits_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite string_of_list_app, IHp by lia.
        simpl.
        rewrite ascii_of_48.
        reflexivity.
      * rewrite base_digits_step by (try lia; vm_compute; lia).
        rewrite zpos_xO_div2, zpos_xO_mod2.
        rewrite base_digits_small by lia.
        reflexivity.
    + rewrite base_digits_small by lia.
      reflexivity.
Qed.
Lemma binary_digits_length_pos_le : forall n,
  0 < n ->
  Zlength (binary_digits n) <= n.
Proof.
  intros n Hn.
  unfold binary_digits.
  apply base_digits_length_pos_le; lia.
Qed.
Lemma binary_digits_nonempty : forall n,
  binary_digits n <> [].
Proof.
  intros n.
  unfold binary_digits.
  apply base_digits_nonempty.
Qed.
Lemma binary_count_state_init : forall orig,
  0 < orig ->
  binary_count_state orig orig 0.
Proof.
  intros orig Horig.
  unfold binary_count_state.
  apply base_count_state_init; lia.
Qed.
Lemma binary_count_state_step : forall orig t digits,
  0 < t ->
  binary_count_state orig t digits ->
  binary_count_state orig (t / 2) (digits + 1).
Proof.
  intros orig t digits Ht Hstate.
  unfold binary_count_state in *.
  apply base_count_state_step; lia || exact Hstate.
Qed.
Lemma binary_count_state_done : forall orig digits,
  0 < orig ->
  binary_count_state orig 0 digits ->
  digits = Zlength (binary_digits orig).
Proof.
  intros orig digits Horig Hstate.
  unfold binary_count_state, binary_digits in *.
  apply base_count_state_done; lia || exact Hstate.
Qed.
Lemma binary_count_state_step_safe : forall orig t digits,
  0 < orig ->
  orig < INT_MAX ->
  0 < t ->
  binary_count_state orig t digits ->
  digits + 1 < INT_MAX.
Proof.
  intros orig t digits Horig Hbound Ht [_ [Hdigits Hlen]].
  unfold binary_digits.
  unfold base_digits_pos in Hlen.
  replace (Z.leb t 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb orig 0) with false in Hlen by (symmetry; apply Z.leb_gt; lia).
  destruct (base_digits t 2) eqn:Hbd.
  - exfalso. apply (base_digits_nonempty t 2). exact Hbd.
  - rewrite Zlength_cons in Hlen.
    pose proof (Zlength_nonneg l).
    pose proof (base_digits_length_pos_le orig 2 Horig ltac:(lia)).
    lia.
Qed.
Lemma binary_fill_full_state_init : forall orig,
  0 < orig ->
  binary_fill_full_state orig orig (Zlength (binary_digits orig))
    (repeat_Z 0 (Zlength (binary_digits orig))).
Proof.
  intros orig Horig.
  unfold binary_fill_full_state, binary_digits.
  apply base_fill_full_state_init; lia.
Qed.
Lemma binary_fill_full_state_step : forall orig x digits out_l,
  0 < x ->
  0 <= digits ->
  binary_fill_full_state orig x (digits + 1) out_l ->
  binary_fill_full_state orig (x / 2) digits
    (replace_Znth digits (signed_last_nbits (48 + x mod 2) 8) out_l).
Proof.
  intros orig x digits out_l Hx Hdigits Hstate.
  unfold binary_fill_full_state in *.
  apply base_fill_full_state_step; lia || exact Hstate.
Qed.
Lemma binary_fill_full_state_done : forall orig out_l,
  binary_fill_full_state orig 0 0 out_l ->
  out_l = binary_digits orig.
Proof.
  intros orig out_l Hstate.
  unfold binary_fill_full_state, binary_digits in *.
  apply base_fill_full_state_done; exact Hstate.
Qed.
Lemma problem_103_spec_neg : forall n m,
  n > m ->
  problem_103_spec n m [45; 49].
Proof.
  intros n m Hgt.
  unfold problem_103_spec, problem_103_spec, rounded_avg_impl.
  rewrite string_of_list_neg1.
  replace (n >? m) with true by (symmetry; apply Z.gtb_gt; lia).
  reflexivity.
Qed.
Lemma problem_103_spec_binary : forall n m out_l,
  n <= m ->
  0 <= avg_103 n m ->
  out_l = binary_digits (avg_103 n m) ->
  problem_103_spec n m out_l.
Proof.
  intros n m out_l Hle Havg Hout.
  subst out_l.
  unfold avg_103 in Havg.
  unfold problem_103_spec, problem_103_spec, rounded_avg_impl, avg_103.
  destruct (Z.gtb_spec n m) as [Hgt | Hngt]; [lia | simpl].
  unfold binary_digits.
  apply base_digits_two_to_binary.
  lia.
Qed.


Lemma proof_of_p103_rounded_avg_safety_wit_24 : p103_rounded_avg_safety_wit_24.
Proof.
  unfold p103_rounded_avg_safety_wit_24.
  intros.
  pre_process.
  assert (total <= num) by
    (subst total; apply binary_digits_length_pos_le; lia).
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_safety_wit_28 : p103_rounded_avg_safety_wit_28.
Proof.
  unfold p103_rounded_avg_safety_wit_28.
  intros.
  pre_process.
  pose proof (Z.rem_bound_pos num 2 ltac:(lia) ltac:(lia)).
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_1 : p103_rounded_avg_entail_wit_1.
Proof.
  unfold p103_rounded_avg_entail_wit_1.
  intros.
  pre_process.
  replace ((n_pre + m_pre) ÷ 2) with ((n_pre + m_pre) / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_init.
    unfold avg_103. apply Z.div_str_pos; lia.
  - unfold avg_103. apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
  - apply Z.div_str_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_2 : p103_rounded_avg_entail_wit_2.
Proof.
  unfold p103_rounded_avg_entail_wit_2.
  intros.
  pre_process.
  replace (t ÷ 2) with (t / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  entailer!.
  - apply binary_count_state_step; lia || assumption.
  - apply binary_count_state_step_safe with (orig := num) (t := t); lia || assumption.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_3 : p103_rounded_avg_entail_wit_3.
Proof.
  unfold p103_rounded_avg_entail_wit_3.
  intros.
  pre_process.
  assert (t = 0) by lia; subst t.
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - unfold CharArray.undef_full, CharArray.undef_seg.
    unfold store_undef_array.
    replace (digits + 1 - 0) with (digits + 1) by lia.
    entailer!.
  - apply binary_count_state_done; lia || assumption.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_4 : p103_rounded_avg_entail_wit_4.
Proof.
  unfold p103_rounded_avg_entail_wit_4.
  intros.
  pre_process.
  rewrite repeat_Z_tail by lia.
  entailer!.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_5 : p103_rounded_avg_entail_wit_5.
Proof.
  unfold p103_rounded_avg_entail_wit_5.
  intros.
  pre_process.
  assert (i = total + 1) by lia; subst i.
  rewrite (CharArray.undef_seg_empty out (total + 1)).
  Exists (repeat_Z 0 total).
  entailer!.
  - rewrite naive_C_Rules.repeat_Z_tail
      by (pose proof (Zlength_nonneg (binary_digits num)); lia).
    unfold naive_C_Rules.repeat_Z, repeat_Z.
    entailer!.
  - subst digits. subst total. apply binary_fill_full_state_init; lia.
  - rewrite Zlength_repeat_Z by
      (pose proof (Zlength_nonneg (binary_digits num)); lia).
    lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_6 : p103_rounded_avg_entail_wit_6.
Proof.
  unfold p103_rounded_avg_entail_wit_6.
  intros.
  pre_process.
  subst orig.
  Exists out_l_2.
  entailer!.
  pose proof (Zlength_nonneg (binary_digits num)).
  lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_7 : p103_rounded_avg_entail_wit_7.
Proof.
  unfold p103_rounded_avg_entail_wit_7.
  intros.
  pre_process.
  Exists out_l_2.
  entailer!.
  - replace (digits - 1 + 1) with digits by lia.
    assumption.
  - pose proof (base_fill_full_state_positive_digits orig 2 num digits out_l_2
      ltac:(lia) ltac:(lia) H14).
    lia.
Qed. 

Lemma proof_of_p103_rounded_avg_entail_wit_8 : p103_rounded_avg_entail_wit_8.
Proof.
  unfold p103_rounded_avg_entail_wit_8.
  intros.
  pre_process.
  replace (num ÷ 2) with (num / 2)
    by (symmetry; apply Z.quot_div_nonneg; lia).
  replace (Z.rem num 2) with (num mod 2)
    by (symmetry; apply Z.rem_mod_nonneg; lia).
  Exists (replace_Znth digits (signed_last_nbits (48 + num mod 2) 8) out_l_2).
  rewrite replace_Znth_app_l by lia.
  entailer!.
  - apply binary_fill_full_state_step; lia || assumption.
  - rewrite Zlength_replace_Znth_44 by lia. lia.
  - apply Z.div_pos; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_return_wit_1 : p103_rounded_avg_return_wit_1.
Proof.
  unfold p103_rounded_avg_return_wit_1.
  intros.
  pre_process.
  assert (num = 0) by lia; subst num.
  unfold binary_fill_full_state in H14.
  destruct H14 as [suffix [[_ [_ [Hdigits Hsplit]]] Hout]].
  unfold base_digits_pos in Hdigits.
  replace (Z.leb 0 0) with true in Hdigits by (symmetry; apply Z.leb_le; lia).
  simpl in Hdigits. subst digits.
  simpl in Hsplit. subst suffix.
  unfold repeat_Z in Hout. simpl in Hout. subst out_l_2.
  Exists (binary_digits orig) (Zlength (binary_digits orig)).
  replace (Zlength (binary_digits orig) + 1) with (total + 1) by lia.
  entailer!.
  - apply problem_103_spec_binary; try lia.
    match goal with
    | H: orig = avg_103 n_pre m_pre |- _ => rewrite H; reflexivity
    end.
  - pose proof (binary_digits_length_pos_le orig ltac:(lia)).
    lia.
  - pose proof (binary_digits_nonempty orig) as Hnonempty.
    destruct (binary_digits orig) eqn:Hbd; [contradiction | idtac].
    rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
  - intros k Hk.
    apply binary_digits_nonzero; lia.
Qed. 

Lemma proof_of_p103_rounded_avg_return_wit_2 : p103_rounded_avg_return_wit_2.
Proof.
  unfold p103_rounded_avg_return_wit_2.
  intros.
  pre_process.
  Exists ((45 :: 49 :: nil) : list Z) 2.
  rewrite (CharArray.undef_seg_empty retval 3).
  entailer!.
  - change (List.app (45 :: 49 :: nil) (0 :: nil)) with (45 :: 49 :: 0 :: nil).
    rewrite (CharArray.full_unfold retval (2 + 1) (49 :: 0 :: nil) 45).
    rewrite (CharArray.seg_unfold retval 1 (2 + 1) (0 :: nil) 49).
    rewrite (CharArray.seg_unfold retval 2 (2 + 1) nil 0).
    rewrite (CharArray.seg_empty retval 3 3).
    entailer!.
  - apply problem_103_spec_neg; lia.
  - intros k Hk.
    assert (Hcase : k = 0 \/ k = 1) by lia.
    destruct Hcase as [-> | ->]; unfold Znth; simpl; lia.
Qed. 
