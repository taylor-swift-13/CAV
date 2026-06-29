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
From SimpleC.EE.CAV.ground_truth_p027_filp_case Require Import p027_filp_case_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import String Ascii Arith Bool.

Import naive_C_Rules.
Require Import p027_filp_case.
Local Open Scope sac.
Require Import Coq.Strings.Ascii.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p027_filp_case.v so public contract files expose definitions only. *)

Lemma string_of_list_length_nat : forall l,
  String.length (string_of_list l) = List.length l.
Proof.
  induction l; simpl; auto.
Qed.
Lemma string_get_string_of_list_nth : forall l i,
  (i < List.length l)%nat ->
  String.get i (string_of_list l) =
    Some (ascii_of (Znth (Z.of_nat i) l 0)).
Proof.
  induction l as [| x xs IH]; intros [| i] Hi; simpl in *; try lia.
  - unfold Znth. simpl. reflexivity.
  - rewrite Znth_cons by lia.
    replace (Z.pos (Pos.of_succ_nat i) - 1) with (Z.of_nat i) by lia.
    apply IH. lia.
Qed.
Lemma nat_of_ascii_ascii_of : forall c,
  0 <= c <= 127 ->
  nat_of_ascii (ascii_of c) = Z.to_nat c.
Proof.
  intros c Hc.
  unfold ascii_of.
  apply nat_ascii_embedding.
  lia.
Qed.
Lemma flip_char_range : forall c,
  0 <= c <= 127 ->
  0 <= flip_char c <= 127.
Proof.
  unfold flip_char.
  intros c Hrange.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.
Lemma flip_char_nonzero : forall c,
  0 <= c <= 127 ->
  c <> 0 ->
  flip_char c <> 0.
Proof.
  unfold flip_char.
  intros c Hrange Hnz.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.
Lemma IsLow_ascii_of_to_is_lower : forall c,
  0 <= c <= 127 ->
  IsLow (ascii_of c) ->
  is_lower c.
Proof.
  unfold IsLow, is_lower.
  intros c Hrange H.
  rewrite nat_of_ascii_ascii_of in H by lia.
  cbn in H.
  lia.
Qed.
Lemma IsUp_ascii_of_to_is_upper : forall c,
  0 <= c <= 127 ->
  IsUp (ascii_of c) ->
  is_upper c.
Proof.
  unfold IsUp, is_upper.
  intros c Hrange H.
  rewrite nat_of_ascii_ascii_of in H by lia.
  cbn in H.
  lia.
Qed.
Lemma Upper_ascii_of_lower : forall c,
  is_lower c ->
  Upper (ascii_of c) = ascii_of (flip_char c).
Proof.
  unfold is_lower, flip_char.
  intros c Hc.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  end.
  simpl.
  unfold Upper.
  rewrite nat_of_ascii_ascii_of by lia.
  replace ((nat_of_ascii "a" <=? Z.to_nat c)%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  replace ((Z.to_nat c <=? nat_of_ascii "z")%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  simpl.
  unfold ascii_of.
  replace (Z.to_nat (c - 32)) with (Z.to_nat c - 32)%nat by lia.
  reflexivity.
Qed.
Lemma Lower_ascii_of_upper : forall c,
  is_upper c ->
  Lower (ascii_of c) = ascii_of (flip_char c).
Proof.
  unfold is_upper, flip_char.
  intros c Hc.
  replace (Z.leb 97 c) with false by (symmetry; apply Z.leb_gt; lia).
  replace (Z.leb 65 c) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb c 90) with true by (symmetry; apply Z.leb_le; lia).
  simpl.
  unfold Lower.
  rewrite nat_of_ascii_ascii_of by lia.
  replace ((nat_of_ascii "A" <=? Z.to_nat c)%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  replace ((Z.to_nat c <=? nat_of_ascii "Z")%nat) with true
    by (symmetry; apply Nat.leb_le; cbn; lia).
  simpl.
  unfold ascii_of.
  replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
  reflexivity.
Qed.
Lemma flip_char_other : forall c,
  0 <= c <= 127 ->
  ~ IsLow (ascii_of c) ->
  ~ IsUp (ascii_of c) ->
  flip_char c = c.
Proof.
  intros c Hrange Hnotlow Hnotup.
  unfold flip_char.
  destruct (Z.leb_spec 97 c); simpl.
  - destruct (Z.leb_spec c 122); simpl.
    + exfalso. apply Hnotlow.
      unfold IsLow.
      rewrite nat_of_ascii_ascii_of by lia.
      cbn. lia.
    + destruct (Z.leb_spec 65 c); simpl.
      * destruct (Z.leb_spec c 90); simpl; [lia | reflexivity].
      * reflexivity.
  - destruct (Z.leb_spec 65 c); simpl.
    + destruct (Z.leb_spec c 90); simpl.
      * exfalso. apply Hnotup.
        unfold IsUp.
        rewrite nat_of_ascii_ascii_of by lia.
        cbn. lia.
      * reflexivity.
    + reflexivity.
Qed.
Lemma problem_27_spec_intro : forall input output n,
  char_range input ->
  Zlength input = n ->
  Zlength output = n ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = flip_char (Znth k input 0)) ->
  problem_27_spec input output.
Proof.
  intros input output n Hrange Hin Hout Hpoint.
  unfold problem_27_spec.
  split.
  - rewrite !string_of_list_length_nat.
    apply Nat2Z.inj.
    rewrite <- !Zlength_correct.
    lia.
  - intros i c Hi Hget.
    assert (Hiz : 0 <= Z.of_nat i < Zlength input).
    {
      split; [lia |].
      rewrite string_of_list_length_nat in Hi.
      apply Nat2Z.inj_lt in Hi.
      rewrite <- Zlength_correct in Hi.
      lia.
    }
    pose proof (string_get_string_of_list_nth input i) as Hin_get.
    specialize (Hin_get ltac:(rewrite <- string_of_list_length_nat; exact Hi)).
    rewrite Hget in Hin_get.
    inversion Hin_get; subst c; clear Hin_get.
    pose proof (Hrange (Z.of_nat i) Hiz) as Hchar.
    assert (Houtz : 0 <= Z.of_nat i < Zlength output) by lia.
    rewrite (string_get_string_of_list_nth output i).
    2:{
      apply Nat2Z.inj_lt.
      rewrite <- Zlength_correct.
      lia.
    }
    rewrite Hpoint by lia.
    split.
    + intro Hlow.
      pose proof (IsLow_ascii_of_to_is_lower _ Hchar Hlow) as Hzlow.
      rewrite <- Upper_ascii_of_lower by exact Hzlow.
      reflexivity.
    + split.
      * intro Hup.
        pose proof (IsUp_ascii_of_to_is_upper _ Hchar Hup) as Hzup.
        rewrite <- Lower_ascii_of_upper by exact Hzup.
        reflexivity.
      * intros [Hnotlow Hnotup].
        rewrite (flip_char_other _ Hchar Hnotlow Hnotup).
        reflexivity.
Qed.


Ltac flip_pre :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simplify_flip :=
  unfold flip_char;
  repeat match goal with
  | H : ?x <= ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?y >= ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with true by (symmetry; apply Z.leb_le; lia)
  | H : ?x > ?y |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  | H : ?y < ?x |- context[Z.leb ?x ?y] =>
      replace (Z.leb x y) with false by (symmetry; apply Z.leb_gt; lia)
  end;
  simpl.

Ltac rewrite_signed_char :=
  repeat match goal with
  | |- context[signed_last_nbits ?x 8] =>
      rewrite (signed_last_nbits_eq x 8) by lia
  end.

Ltac solve_step_value input ol idx :=
  intros k Hk;
  destruct (Z_lt_ge_dec k idx) as [Hlt | Hge];
  [ rewrite app_Znth1 by
      (match goal with
       | Hlen : Zlength ol = idx |- _ => rewrite Hlen; lia
       end);
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k ol 0 = flip_char (Znth k input 0) |- _ =>
        apply Hprefix; lia
    end
  | assert (k = idx) by lia;
    subst k;
    rewrite app_Znth2 by
      (match goal with
       | Hlen : Zlength ol = idx |- _ => rewrite Hlen; lia
       end);
    match goal with
    | Hlen : Zlength ol = idx |- _ =>
        replace (idx - Zlength ol) with 0 by lia
    end;
    rewrite Znth0_cons;
    repeat rewrite app_Znth1 in * by lia;
    repeat match goal with
    | Hrange : char_range ?xs |- context[signed_last_nbits (Znth ?pos ?xs 0) 8] =>
        let Hr := fresh "Hchar" in
        pose proof (Hrange pos ltac:(lia)) as Hr;
        rewrite (signed_last_nbits_eq (Znth pos xs 0) 8) by lia
    end;
    unfold flip_char;
    repeat match goal with
    | |- context[Z.leb ?x ?y] =>
        destruct (Z.leb_spec x y); simpl
    end;
    lia ].

Ltac solve_step_with input ol idx v :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia;
  Exists (app ol (cons v nil));
  entailer!;
  [ solve_step_value input ol idx
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_p027_filp_case_entail_wit_1 : p027_filp_case_entail_wit_1.
Proof.
  unfold p027_filp_case_entail_wit_1.
  intros.
  flip_pre.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  lia.
Qed. 

Lemma proof_of_p027_filp_case_entail_wit_2_1 : p027_filp_case_entail_wit_2_1.
Proof.
  unfold p027_filp_case_entail_wit_2_1.
  intros.
  solve_step_with l out_l_2 i (Znth i l 0).
Qed. 

Lemma proof_of_p027_filp_case_entail_wit_2_2 : p027_filp_case_entail_wit_2_2.
Proof.
  unfold p027_filp_case_entail_wit_2_2.
  intros.
  solve_step_with l out_l_2 i (signed_last_nbits (Znth i l 0) 8).
Qed. 

Lemma proof_of_p027_filp_case_entail_wit_2_3 : p027_filp_case_entail_wit_2_3.
Proof.
  unfold p027_filp_case_entail_wit_2_3.
  intros.
  solve_step_with l out_l_2 i (signed_last_nbits (Znth i l 0) 8).
Qed. 

Lemma proof_of_p027_filp_case_entail_wit_2_4 : p027_filp_case_entail_wit_2_4.
Proof.
  unfold p027_filp_case_entail_wit_2_4.
  intros.
  solve_step_with l out_l_2 i (Znth i l 0 + 32).
Qed. 

Lemma proof_of_p027_filp_case_entail_wit_2_5 : p027_filp_case_entail_wit_2_5.
Proof.
  unfold p027_filp_case_entail_wit_2_5.
  intros.
  solve_step_with l out_l_2 i (Znth i l 0 - 32).
Qed. 

Lemma proof_of_p027_filp_case_return_wit_1 : p027_filp_case_return_wit_1.
Proof.
  unfold p027_filp_case_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  match goal with
  | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
  end.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - apply problem_27_spec_intro with (n := len); try lia; try assumption.
    intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char (Znth k l 0) |- _ =>
        apply Hprefix; lia
    end.
  - intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char (Znth k l 0),
      Hrange : char_range l,
      Hnz : forall k : Z, _ -> Znth k l 0 <> 0 |- _ =>
        rewrite Hprefix by lia;
        apply flip_char_nonzero;
        [apply Hrange | apply Hnz]; lia
    end.
Qed. 
