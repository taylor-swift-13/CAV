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
From SimpleC.EE Require Import p144_simplify_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.

Import naive_C_Rules.
Require Import p144_simplify.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p144_simplify.v so public contract files expose definitions only. *)

Lemma parse_digits_aux_app_single : forall l c acc,
  parse_digits_z_aux (l ++ [c]) acc =
  parse_digits_z_aux l acc * 10 + digit_value c.
Proof.
  induction l as [| x xs IH]; intros c acc; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma parse_digits_snoc : forall l c,
  parse_digits (l ++ [c]) =
  parse_digits l * 10 + digit_value c.
Proof.
  intros l c.
  unfold parse_digits.
  apply parse_digits_aux_app_single.
Qed.
Lemma parse_digits_empty : forall l i,
  parse_digits (sublist i i l) = 0.
Proof.
  intros.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma Znth_app_left : forall (l1 l2 : list Z) i d,
  0 <= i < Zlength l1 ->
  Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 i d Hi.
  unfold Znth.
  rewrite app_nth1.
  - reflexivity.
  - rewrite Zlength_correct in Hi.
    assert ((Z.to_nat i < Datatypes.length l1)%nat).
    { apply Nat2Z.inj_lt.
      rewrite Z2Nat.id by lia.
      lia. }
    lia.
Qed.
Lemma parse_digits_step_sublist : forall l lo i,
  0 <= lo <= i ->
  i < Zlength l ->
  parse_digits (sublist lo (i + 1) l) =
    parse_digits (sublist lo i l) * 10 + digit_value (Znth i l 0).
Proof.
  intros l lo i Hlo Hi.
  rewrite (sublist_split lo (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  apply parse_digits_snoc.
Qed.
Lemma fraction_parts_num_digit : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  digit_char (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.
Lemma fraction_parts_slash_char : forall s slash num den,
  fraction_parts s slash num den ->
  Znth slash s 0 = 47.
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.
Lemma fraction_parts_den_digit : forall s slash num den i,
  fraction_parts s slash num den ->
  slash < i < Zlength s ->
  digit_char (Znth i s 0).
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & Hdigits & _).
  apply Hdigits; lia.
Qed.
Lemma fraction_parts_num_value : forall s slash num den,
  fraction_parts s slash num den ->
  num = parse_digits (sublist 0 slash s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.
Lemma fraction_parts_den_value : forall s slash num den,
  fraction_parts s slash num den ->
  den = parse_digits (sublist (slash + 1) (Zlength s) s).
Proof.
  intros s slash num den Hparts.
  unfold fraction_parts in Hparts.
  tauto.
Qed.
Lemma fraction_parts_prefix_num_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  0 <= parse_digits (sublist 0 i s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.
Lemma fraction_parts_prefix_den_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i <= Zlength s ->
  0 <= parse_digits (sublist (slash + 1) i s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  unfold fraction_parts in Hparts.
  destruct Hparts as (_ & _ & _ & _ & _ & _ & _ & Hprefix & _).
  apply Hprefix; lia.
Qed.
Lemma fraction_parts_slash_char_app : forall s slash num den,
  fraction_parts s slash num den ->
  Znth slash (s ++ [0]) 0 = 47.
Proof.
  intros s slash num den Hparts.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  apply fraction_parts_slash_char with (num := num) (den := den).
  exact Hparts.
Qed.
Lemma fraction_parts_num_loop_lt : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 <> 47 ->
  i < slash.
Proof.
  intros s slash num den i Hparts Hi Hneq.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [exact Hlt |].
  assert (i = slash) by lia.
  subst.
  exfalso.
  apply Hneq.
  apply fraction_parts_slash_char_app with (num := num) (den := den).
  exact Hparts.
Qed.
Lemma fraction_parts_num_digit_app : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  digit_char (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  exact (fraction_parts_num_digit s slash num den i Hparts Hi).
Qed.
Lemma fraction_parts_den_digit_app : forall s slash num den i,
  fraction_parts s slash num den ->
  slash < i < Zlength s ->
  digit_char (Znth i (s ++ [0]) 0).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  exact (fraction_parts_den_digit s slash num den i Hparts Hi).
Qed.
Lemma fraction_parts_num_step_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  0 <= parse_digits (sublist 0 (i + 1) s) <= num.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_prefix_num_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.
Lemma fraction_parts_den_step_bound : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i < Zlength s ->
  0 <= parse_digits (sublist (slash + 1) (i + 1) s) <= den.
Proof.
  intros s slash num den i Hparts Hi.
  exact (fraction_parts_prefix_den_bound s slash num den (i + 1) Hparts ltac:(lia)).
Qed.
Lemma fraction_parts_den_done : forall s slash num den i d,
  fraction_parts s slash num den ->
  i >= Zlength s ->
  i <= Zlength s ->
  d = parse_digits (sublist (slash + 1) i s) ->
  d = den.
Proof.
  intros s slash num den i d Hparts Hge Hle Hd.
  assert (i = Zlength s) by lia.
  subst i.
  rewrite Hd.
  symmetry.
  apply fraction_parts_den_value with (slash := slash) (num := num).
  exact Hparts.
Qed.
Lemma fraction_parts_num_step_value : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i < slash ->
  parse_digits (sublist 0 (i + 1) s) =
    parse_digits (sublist 0 i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  unfold digit_value.
  rewrite parse_digits_step_sublist by (unfold fraction_parts in Hparts; lia).
  reflexivity.
Qed.
Lemma fraction_parts_den_step_value : forall s slash num den i,
  fraction_parts s slash num den ->
  slash + 1 <= i < Zlength s ->
  parse_digits (sublist (slash + 1) (i + 1) s) =
    parse_digits (sublist (slash + 1) i s) * 10 + (Znth i (s ++ [0]) 0 - 48).
Proof.
  intros s slash num den i Hparts Hi.
  rewrite Znth_app_left by (unfold fraction_parts in Hparts; lia).
  unfold digit_value.
  rewrite parse_digits_step_sublist by (unfold fraction_parts in Hparts; lia).
  reflexivity.
Qed.
Lemma fraction_parts_slash_index : forall s slash num den i,
  fraction_parts s slash num den ->
  0 <= i <= slash ->
  Znth i (s ++ [0]) 0 = 47 ->
  i = slash.
Proof.
  intros s slash num den i Hparts Hi Hchar.
  destruct (Z_lt_ge_dec i slash) as [Hlt | Hge]; [| lia].
  rewrite Znth_app_left in Hchar by (unfold fraction_parts in Hparts; lia).
  pose proof (fraction_parts_num_digit s slash num den i Hparts ltac:(lia)) as Hdigit.
  unfold digit_char in Hdigit.
  lia.
Qed.
Lemma problem_144_spec_intro : forall x n sx sn a b c d output,
  fraction_parts x sx a b ->
  fraction_parts n sn c d ->
  fraction_values_safe a b c d ->
  output = (if Z.eqb (Z.rem (a * c) (b * d)) 0 then 1 else 0) ->
  problem_144_spec x n output.
Proof.
  intros x n sx sn a b c d output Hx Hn _ Hout.
  subst output.
  unfold problem_144_spec.
  exists sx, sn, a, b, c, d.
  split; [exact Hx |].
  split; [exact Hn |].
  unfold bool_of.
  destruct (Z.eqb (Z.rem (a * c) (b * d)) 0); reflexivity.
Qed.


Ltac open_safe_values_144 :=
  repeat match goal with
  | H : fraction_values_safe _ _ _ _ |- _ =>
      unfold fraction_values_safe in H;
      destruct H as ((? & ?) & (? & ?) & (? & ?) & (? & ?))
  end.

Ltac add_char_digit_144 :=
  match goal with
  | Hparts : fraction_parts ?s ?slash ?num ?den,
    Hneq : Znth ?i (app ?s (cons 0 nil)) 0 <> 47 |- context[Znth ?i (app ?s (cons 0 nil)) 0] =>
      let Hlt := fresh "Hlt" in
      let Hdig := fresh "Hdig" in
      pose proof (fraction_parts_num_loop_lt s slash num den i Hparts ltac:(lia) Hneq) as Hlt;
      pose proof (fraction_parts_num_digit_app s slash num den i Hparts ltac:(lia)) as Hdig;
      unfold digit_char in Hdig
  | Hparts : fraction_parts ?s ?slash ?num ?den |- context[Znth ?i (app ?s (cons 0 nil)) 0] =>
      let Hdig := fresh "Hdig" in
      pose proof (fraction_parts_den_digit_app s slash num den i Hparts ltac:(lia)) as Hdig;
      unfold digit_char in Hdig
  end.

Ltac solve_safety_144 :=
  pre_process;
  subst;
  entailer!;
  open_safe_values_144;
  try add_char_digit_144;
  try nia.

Ltac solve_basic_entail_144 :=
  pre_process;
  subst;
  entailer!;
  try rewrite parse_digits_empty;
  open_safe_values_144;
  unfold fraction_parts in *;
  try nia.

Ltac solve_num_step_144 :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hparts : fraction_parts ?s ?slash ?num ?den,
    Hneq : Znth ?i (app ?s (cons 0 nil)) 0 <> 47 |- _ =>
      let Hlt := fresh "Hlt" in
      let Hstep := fresh "Hstep" in
      let Hbound := fresh "Hbound" in
      pose proof (fraction_parts_num_loop_lt s slash num den i Hparts ltac:(lia) Hneq) as Hlt;
      pose proof (fraction_parts_num_step_value s slash num den i Hparts ltac:(lia)) as Hstep;
      pose proof (fraction_parts_num_step_bound s slash num den i Hparts ltac:(lia)) as Hbound;
      try rewrite Hstep;
      try rewrite <- Hstep;
      lia
  end.

Ltac solve_den_step_144 :=
  pre_process;
  subst;
  entailer!;
  match goal with
  | Hparts : fraction_parts ?s ?slash ?num ?den,
    Hlo : ?slash + 1 <= ?i,
    Hhi : ?i < Zlength ?s |- _ =>
      let Hstep := fresh "Hstep" in
      let Hbound := fresh "Hbound" in
      pose proof (fraction_parts_den_step_value s slash num den i Hparts ltac:(lia)) as Hstep;
      pose proof (fraction_parts_den_step_bound s slash num den i Hparts ltac:(lia)) as Hbound;
      try rewrite Hstep;
      try rewrite <- Hstep;
      lia
  end.

Lemma proof_of_p144_simplify_safety_wit_7 : p144_simplify_safety_wit_7.
Proof.
  unfold p144_simplify_safety_wit_7.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_8 : p144_simplify_safety_wit_8.
Proof.
  unfold p144_simplify_safety_wit_8.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_9 : p144_simplify_safety_wit_9.
Proof.
  unfold p144_simplify_safety_wit_9.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_15 : p144_simplify_safety_wit_15.
Proof.
  unfold p144_simplify_safety_wit_15.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_16 : p144_simplify_safety_wit_16.
Proof.
  unfold p144_simplify_safety_wit_16.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_17 : p144_simplify_safety_wit_17.
Proof.
  unfold p144_simplify_safety_wit_17.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_23 : p144_simplify_safety_wit_23.
Proof.
  unfold p144_simplify_safety_wit_23.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_24 : p144_simplify_safety_wit_24.
Proof.
  unfold p144_simplify_safety_wit_24.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_25 : p144_simplify_safety_wit_25.
Proof.
  unfold p144_simplify_safety_wit_25.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_31 : p144_simplify_safety_wit_31.
Proof.
  unfold p144_simplify_safety_wit_31.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_32 : p144_simplify_safety_wit_32.
Proof.
  unfold p144_simplify_safety_wit_32.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_33 : p144_simplify_safety_wit_33.
Proof.
  unfold p144_simplify_safety_wit_33.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_37 : p144_simplify_safety_wit_37.
Proof.
  unfold p144_simplify_safety_wit_37.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_38 : p144_simplify_safety_wit_38.
Proof.
  unfold p144_simplify_safety_wit_38.
  intros.
  solve_safety_144.
Qed. 

Lemma proof_of_p144_simplify_safety_wit_39 : p144_simplify_safety_wit_39.
Proof.
  unfold p144_simplify_safety_wit_39.
  intros.
  pre_process.
  subst.
  entailer!;
  open_safe_values_144;
  match goal with
  | Hparts : fraction_parts ?s ?slash ?num ?den |- context[parse_digits (sublist (?slash + 1) ?i ?s)] =>
      assert (parse_digits (sublist (slash + 1) i s) = den) by
        (assert (i = Zlength s) by lia;
         subst i;
         symmetry;
         eapply fraction_parts_den_value; eauto)
  end;
  nia.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_1 : p144_simplify_entail_wit_1.
Proof.
  unfold p144_simplify_entail_wit_1.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_2 : p144_simplify_entail_wit_2.
Proof.
  unfold p144_simplify_entail_wit_2.
  intros.
  solve_num_step_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_3 : p144_simplify_entail_wit_3.
Proof.
  unfold p144_simplify_entail_wit_3.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = sx) by (eapply fraction_parts_slash_index; eauto; lia).
  subst i.
  assert (Hax : parse_digits (sublist 0 sx lx) = ax) by
    (symmetry; eapply fraction_parts_num_value; eauto).
  rewrite Hax.
  entailer!.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_4 : p144_simplify_entail_wit_4.
Proof.
  unfold p144_simplify_entail_wit_4.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_5 : p144_simplify_entail_wit_5.
Proof.
  unfold p144_simplify_entail_wit_5.
  intros.
  solve_den_step_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_6 : p144_simplify_entail_wit_6.
Proof.
  unfold p144_simplify_entail_wit_6.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = Zlength lx) by lia.
  subst i.
  assert (Hbx : parse_digits (sublist (sx + 1) (Zlength lx) lx) = bx) by
    (symmetry; eapply fraction_parts_den_value; eauto).
  rewrite Hbx.
  entailer!.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_8 : p144_simplify_entail_wit_8.
Proof.
  unfold p144_simplify_entail_wit_8.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_9 : p144_simplify_entail_wit_9.
Proof.
  unfold p144_simplify_entail_wit_9.
  intros.
  solve_num_step_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_10 : p144_simplify_entail_wit_10.
Proof.
  unfold p144_simplify_entail_wit_10.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (i = sn) by (eapply fraction_parts_slash_index; eauto; lia).
  subst i.
  assert (Hcn : parse_digits (sublist 0 sn ln) = cn) by
    (symmetry; eapply fraction_parts_num_value; eauto).
  rewrite Hcn.
  entailer!.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_11 : p144_simplify_entail_wit_11.
Proof.
  unfold p144_simplify_entail_wit_11.
  intros.
  solve_basic_entail_144.
Qed. 

Lemma proof_of_p144_simplify_entail_wit_12 : p144_simplify_entail_wit_12.
Proof.
  unfold p144_simplify_entail_wit_12.
  intros.
  solve_den_step_144.
Qed. 

Lemma proof_of_p144_simplify_return_wit_1 : p144_simplify_return_wit_1.
Proof.
  unfold p144_simplify_return_wit_1.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (Hdn : parse_digits (sublist (sn + 1) i ln) = dn) by
    (assert (i = Zlength ln) by lia;
     subst i;
     symmetry;
     eapply fraction_parts_den_value; eauto).
  apply problem_144_spec_intro with (sx := sx) (sn := sn) (a := ax) (b := bx) (c := cn) (d := dn).
  - eassumption.
  - eassumption.
  - eassumption.
  - rewrite <- Hdn.
    destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * parse_digits (sublist (sn + 1) i ln))) 0).
    + exfalso. apply H. exact e.
    + reflexivity.
Qed. 

Lemma proof_of_p144_simplify_return_wit_2 : p144_simplify_return_wit_2.
Proof.
  unfold p144_simplify_return_wit_2.
  intros.
  pre_process.
  subst.
  entailer!.
  assert (Hdn : parse_digits (sublist (sn + 1) i ln) = dn) by
    (assert (i = Zlength ln) by lia;
     subst i;
     symmetry;
     eapply fraction_parts_den_value; eauto).
  apply problem_144_spec_intro with (sx := sx) (sn := sn) (a := ax) (b := bx) (c := cn) (d := dn).
  - eassumption.
  - eassumption.
  - eassumption.
  - rewrite <- Hdn.
    destruct (Z.eqb_spec (Z.rem (ax * cn) (bx * parse_digits (sublist (sn + 1) i ln))) 0).
    + reflexivity.
    + contradiction.
Qed. 
