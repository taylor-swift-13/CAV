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
From SimpleC.EE.CAV.ground_truth_p051_remove_vowels Require Import p051_remove_vowels_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import p051_remove_vowels.
Local Open Scope sac.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p051_remove_vowels.v so public contract files expose definitions only. *)

Lemma remove_vowels_prefix_0 : forall s,
  remove_vowels_prefix 0 s = [].
Proof.
  intros s.
  unfold remove_vowels_prefix.
  reflexivity.
Qed.
Lemma remove_vowels_list_app : forall l1 l2,
  remove_vowels_list (List.app l1 l2) =
  List.app (remove_vowels_list l1) (remove_vowels_list l2).
Proof.
  induction l1 as [| x xs IH]; intros l2; simpl.
  - reflexivity.
  - destruct (is_vowel x); simpl; rewrite IH; reflexivity.
Qed.
Lemma firstn_succ_snoc_51 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth_51 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_51 with (d := 0) by
    (apply Nat2Z.inj_lt; rewrite Z2Nat.id by lia; rewrite <- Zlength_correct; lia).
  reflexivity.
Qed.
Lemma remove_vowels_prefix_step : forall i s,
  0 <= i ->
  i < Zlength s ->
  remove_vowels_prefix (i + 1) s =
    let prev := remove_vowels_prefix i s in
    let c := Znth i s 0 in
    if is_vowel c then prev else List.app prev [c].
Proof.
  intros i s Hi Hlt.
  unfold remove_vowels_prefix.
  rewrite firstn_succ_Znth_51 by lia.
  rewrite remove_vowels_list_app.
  simpl.
  destruct (is_vowel (Znth i s 0)); simpl; rewrite ?app_nil_r; reflexivity.
Qed.
Lemma remove_vowels_list_length_bound : forall s,
  Zlength (remove_vowels_list s) <= Zlength s.
Proof.
  induction s as [| x xs IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite !Zlength_cons.
    destruct (is_vowel x); simpl; try rewrite Zlength_cons; lia.
Qed.
Lemma remove_vowels_prefix_length_bound : forall i s,
  0 <= i ->
  Zlength (remove_vowels_prefix i s) <= i.
Proof.
  intros i s Hi.
  unfold remove_vowels_prefix.
  eapply Z.le_trans.
  - apply remove_vowels_list_length_bound.
  - rewrite Zlength_correct, length_firstn.
    pose proof (Nat.le_min_l (Z.to_nat i) (Datatypes.length s)) as Hmin.
    apply Nat2Z.inj_le in Hmin.
    rewrite Z2Nat.id in Hmin by lia.
    exact Hmin.
Qed.
Lemma is_vowel_correct : forall c,
  0 <= c <= 127 ->
  is_vowel c = is_vowel_nat (ascii_of c).
Proof.
  intros c Hrange.
  remember (ascii_of c) as a eqn:Ha.
  unfold ascii_of in Ha.
  pose proof (nat_ascii_embedding (Z.to_nat c) ltac:(lia)) as Hnat.
  rewrite <- Ha in Hnat.
  assert (Hc : c = Z.of_nat (nat_of_ascii a)).
  {
    rewrite <- (Z2Nat.id c) by lia.
    rewrite <- Hnat.
    reflexivity.
  }
  subst c.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0, b1, b2, b3, b4, b5, b6, b7; vm_compute; reflexivity.
Qed.
Lemma remove_vowels_list_correct : forall s,
  char_range s ->
  string_of_list (remove_vowels_list s) =
  filter_string (fun c => negb (is_vowel_nat c)) (string_of_list s).
Proof.
  induction s as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - assert (Hcrange : 0 <= c <= 127).
    { pose proof (Zlength_nonneg rest) as Hlen.
      pose proof (Hrange 0 ltac:(rewrite Zlength_cons; lia)) as Hc.
      change (Znth 0 (c :: rest) 0) with c in Hc.
      lia. }
    assert (Hrestrange : char_range rest).
    {
      unfold char_range in *.
      intros i Hi.
      specialize (Hrange (i + 1)).
      replace (Znth i rest 0) with (Znth (i + 1) (c :: rest) 0).
      - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg rest); lia.
      - unfold Znth.
        replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    rewrite <- is_vowel_correct by exact Hcrange.
    destruct (is_vowel c); simpl.
    + apply IH. exact Hrestrange.
    + rewrite IH by exact Hrestrange. reflexivity.
Qed.
Lemma char_range_firstn_all : forall s,
  char_range s ->
  char_range (firstn (Z.to_nat (Zlength s)) s).
Proof.
  intros s Hrange.
  replace (Z.to_nat (Zlength s)) with (List.length s) by
    (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  exact Hrange.
Qed.
Lemma problem_51_spec_intro : forall input output,
  char_range input ->
  output = remove_vowels_prefix (Zlength input) input ->
  problem_51_spec input output.
Proof.
  intros input output Hrange Hout.
  unfold problem_51_spec.
  rewrite Hout.
  unfold remove_vowels_prefix.
  replace (Z.to_nat (Zlength input)) with (List.length input) by
    (rewrite Zlength_correct; lia).
  rewrite firstn_all.
  apply remove_vowels_list_correct.
  exact Hrange.
Qed.


Ltac simplify_vowel_case :=
  repeat rewrite app_Znth1 in * by lia;
  unfold is_vowel;
  repeat match goal with
  | |- context[Z.eqb ?x ?y] =>
      destruct (Z.eqb_spec x y); simpl
  end;
  try lia.

Ltac rewrite_signed_input :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hrange : char_range ?l |- context[signed_last_nbits (Znth ?i ?l 0) 8] =>
      let Hr := fresh "Hchar" in
      pose proof (Hrange i ltac:(lia)) as Hr;
      rewrite (signed_last_nbits_eq (Znth i l 0) 8) by lia
  end.

Ltac solve_appended_nonzero :=
  intros k Hk;
  match goal with
  | Hprefix_nz : forall q : Z, _ -> Znth q ?prefix 0 <> 0,
    Hinput_nz : forall q : Z, _ -> Znth q ?l 0 <> 0
    |- Znth k (app ?prefix (cons (Znth ?i ?l 0) nil)) 0 <> 0 =>
      destruct (Z_lt_ge_dec k (Zlength prefix)) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix_nz; lia
      | assert (k = Zlength prefix) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (Zlength prefix - Zlength prefix) with 0 by lia;
        rewrite Znth0_cons;
        apply Hinput_nz; lia ]
  end.

Ltac solve_vowel_step :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | |- context[CharArray.full ?out ?j (remove_vowels_prefix ?i ?l)] =>
      Exists (remove_vowels_prefix i l)
	  end;
	  entailer!;
	  try (rewrite remove_vowels_prefix_step by lia;
	       simplify_vowel_case;
	       reflexivity).

Ltac solve_nonvowel_step :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia;
  rewrite_signed_input;
  match goal with
  | |- context[CharArray.full ?out (?j + 1) (app (remove_vowels_prefix ?i ?l) (cons (Znth ?i ?l 0) nil))] =>
      Exists (app (remove_vowels_prefix i l) (cons (Znth i l 0) nil))
	  end;
	  entailer!;
	  try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia);
	  try solve_appended_nonzero;
	  try (rewrite remove_vowels_prefix_step by lia;
	       simplify_vowel_case;
	       reflexivity).

Lemma proof_of_p051_remove_vowels_entail_wit_1 : p051_remove_vowels_entail_wit_1.
Proof.
  unfold p051_remove_vowels_entail_wit_1.
  intros.
  pre_process.
  subst.
  Exists nil.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  rewrite remove_vowels_prefix_0.
  entailer!.
  lia.
Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_1 : p051_remove_vowels_entail_wit_2_1.
Proof. unfold p051_remove_vowels_entail_wit_2_1; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_2 : p051_remove_vowels_entail_wit_2_2.
Proof. unfold p051_remove_vowels_entail_wit_2_2; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_3 : p051_remove_vowels_entail_wit_2_3.
Proof. unfold p051_remove_vowels_entail_wit_2_3; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_4 : p051_remove_vowels_entail_wit_2_4.
Proof. unfold p051_remove_vowels_entail_wit_2_4; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_5 : p051_remove_vowels_entail_wit_2_5.
Proof. unfold p051_remove_vowels_entail_wit_2_5; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_6 : p051_remove_vowels_entail_wit_2_6.
Proof. unfold p051_remove_vowels_entail_wit_2_6; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_7 : p051_remove_vowels_entail_wit_2_7.
Proof. unfold p051_remove_vowels_entail_wit_2_7; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_8 : p051_remove_vowels_entail_wit_2_8.
Proof. unfold p051_remove_vowels_entail_wit_2_8; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_9 : p051_remove_vowels_entail_wit_2_9.
Proof. unfold p051_remove_vowels_entail_wit_2_9; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_10 : p051_remove_vowels_entail_wit_2_10.
Proof. unfold p051_remove_vowels_entail_wit_2_10; intros; solve_vowel_step. Qed.

Lemma proof_of_p051_remove_vowels_entail_wit_2_11 : p051_remove_vowels_entail_wit_2_11.
Proof. unfold p051_remove_vowels_entail_wit_2_11; intros; solve_nonvowel_step. Qed.

Lemma proof_of_p051_remove_vowels_return_wit_1 : p051_remove_vowels_return_wit_1.
Proof.
  unfold p051_remove_vowels_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  Exists j.
  entailer!.
  eapply problem_51_spec_intro; eauto.
  rewrite H1.
  assumption.
Qed.
