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
From SimpleC.EE.CAV.ground_truth_p089_encrypt Require Import p089_encrypt_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p089_encrypt.
Local Open Scope sac.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p089_encrypt.v so public contract files expose definitions only. *)

Lemma nat_of_ascii_ascii_of : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.
Lemma encrypt_output_range : forall x,
  lower_char x ->
  97 <= encrypt_char x <= 122.
Proof.
  intros x Hlower.
  unfold encrypt_char, lower_char in *.
  pose proof (Z.rem_bound_pos (x + 4 - 97) 26 ltac:(lia) ltac:(lia)).
  lia.
Qed.
Lemma encrypt_char_nonzero : forall x,
  lower_char x ->
  encrypt_char x <> 0.
Proof.
  intros x Hlower.
  pose proof (encrypt_output_range x Hlower).
  lia.
Qed.
Lemma lower_char_cases : forall x,
  lower_char x ->
  x = 97 \/ x = 98 \/ x = 99 \/ x = 100 \/ x = 101 \/ x = 102 \/
  x = 103 \/ x = 104 \/ x = 105 \/ x = 106 \/ x = 107 \/ x = 108 \/
  x = 109 \/ x = 110 \/ x = 111 \/ x = 112 \/ x = 113 \/ x = 114 \/
  x = 115 \/ x = 116 \/ x = 117 \/ x = 118 \/ x = 119 \/ x = 120 \/
  x = 121 \/ x = 122.
Proof.
  unfold lower_char.
  intros; lia.
Qed.
Lemma encrypt_char_relation : forall x,
  lower_char x ->
  char_relation (ascii_of x) (ascii_of (encrypt_char x)).
Proof.
  intros x Hlower.
  pose proof (lower_char_cases x Hlower) as Hcases.
  repeat
    match type of Hcases with
    | _ \/ _ => destruct Hcases as [-> | Hcases]; [vm_compute; reflexivity |]
    | _ => subst x; vm_compute; reflexivity
    end.
Qed.
Lemma lower_char_from_problem_89_pre : forall s k,
  problem_89_pre s ->
  ascii_range s ->
  0 <= k < Zlength s ->
  lower_char (Znth k s 0).
Proof.
  induction s as [| a rest IH]; intros k Hpre Hrange Hk.
  - rewrite Zlength_nil in Hk; lia.
  - simpl in Hpre.
    destruct Hpre as [Ha Hrest].
    destruct (Z.eq_dec k 0) as [-> | Hnz].
    + unfold is_lowercase_ascii, lower_char in *.
      pose proof (Hrange 0 Hk) as Harange.
      rewrite Znth0_cons in Harange.
      rewrite nat_of_ascii_ascii_of in Ha by exact Harange.
      cbn in Ha.
      destruct Ha as [Ha_low Ha_high].
      apply Nat2Z.inj_le in Ha_low.
      apply Nat2Z.inj_le in Ha_high.
      rewrite Z2Nat.id in Ha_low by lia.
      rewrite Z2Nat.id in Ha_high by lia.
      rewrite Znth0_cons.
      lia.
    + rewrite Znth_cons by lia.
      apply IH.
      * exact Hrest.
      * intros i Hi.
        specialize (Hrange (i + 1) ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth_cons in Hrange by lia.
        replace (i + 1 - 1) with i in Hrange by lia.
        exact Hrange.
      * rewrite Zlength_cons in Hk; lia.
Qed.
Lemma list_ascii_of_string_of_list : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l; simpl; congruence.
Qed.
Lemma problem_89_spec_intro_map : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_89_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encrypt_char (Znth k input 0)) ->
  Forall2 char_relation (map ascii_of input) (map ascii_of output).
Proof.
  induction input as [| x xs IH]; intros output n Hin Hout Hpre Hrange Hpoint.
  - destruct output as [| y ys].
    + constructor.
    + rewrite Zlength_nil in Hin.
      rewrite Zlength_cons in Hout.
      pose proof (Zlength_nonneg ys).
      lia.
  - destruct output as [| y ys].
    + rewrite Zlength_cons in Hin.
      rewrite Zlength_nil in Hout.
      pose proof (Zlength_nonneg xs).
      lia.
    + simpl.
      constructor.
      * assert (Hy : y = encrypt_char x).
        {
          assert (H0n : 0 <= 0 < n).
          { rewrite <- Hin. rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia. }
          specialize (Hpoint 0 H0n).
          rewrite !Znth0_cons in Hpoint.
          exact Hpoint.
        }
        subst y.
        apply encrypt_char_relation.
        eapply lower_char_from_problem_89_pre with (s := x :: xs) (k := 0); eauto.
        rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
      * apply IH with (n := n - 1).
        -- rewrite Zlength_cons in Hin; lia.
        -- rewrite Zlength_cons in Hout; lia.
        -- simpl in Hpre. destruct Hpre as [_ Hpre_tail]. exact Hpre_tail.
        -- intros k Hk.
           specialize (Hrange (k + 1) ltac:(rewrite Zlength_cons; lia)).
           rewrite Znth_cons in Hrange by lia.
           replace (k + 1 - 1) with k in Hrange by lia.
           exact Hrange.
        -- intros k Hk.
           specialize (Hpoint (k + 1) ltac:(rewrite Zlength_cons in Hin; lia)).
           rewrite !Znth_cons in Hpoint by lia.
           replace (k + 1 - 1) with k in Hpoint by lia.
           exact Hpoint.
Qed.
Lemma problem_89_spec_intro : forall input output n,
  Zlength input = n ->
  Zlength output = n ->
  problem_89_pre input ->
  ascii_range input ->
  (forall k, 0 <= k < n ->
    Znth k output 0 = encrypt_char (Znth k input 0)) ->
  problem_89_spec input output.
Proof.
  intros input output n Hin Hout Hpre Hrange Hpoint.
  unfold problem_89_spec.
  rewrite !list_ascii_of_string_of_list.
  eapply problem_89_spec_intro_map; eauto.
Qed.


Ltac encrypt_pre :=
  pre_process;
  repeat rewrite app_Znth1 in * by lia.

Ltac lower_at :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_89_pre ?l,
    Hrange : ascii_range ?l |- context[Znth ?i ?l 0] =>
      let Hlower := fresh "Hlower" in
      pose proof (lower_char_from_problem_89_pre l i Hpre Hrange ltac:(lia)) as Hlower;
      unfold lower_char in Hlower
  end.

Ltac solve_encrypt_safety :=
  encrypt_pre;
  lower_at;
  unfold encrypt_char in *;
  match goal with
  | |- context[((Znth ?i ?l 0 + 4 - 97) % 26)] =>
      pose proof (Z.rem_bound_pos (Znth i l 0 + 4 - 97) 26 ltac:(lia) ltac:(lia))
  | _ => idtac
  end;
  entailer!.

Ltac rewrite_signed_encrypt :=
  repeat rewrite app_Znth1 in * by lia;
  match goal with
  | Hpre : problem_89_pre ?l,
    Hrange : ascii_range ?l |- context[signed_last_nbits ?x 8] =>
      let idx := match x with context[Znth ?i l 0] => i end in
      let Hlower := fresh "Hlower" in
      pose proof (lower_char_from_problem_89_pre l idx Hpre Hrange ltac:(lia)) as Hlower;
      unfold lower_char in Hlower;
      rewrite (signed_last_nbits_eq x 8)
        by (try lia;
            pose proof (Z.rem_bound_pos (Znth idx l 0 + 4 - 97) 26 ltac:(lia) ltac:(lia));
            lia)
  end.

Ltac solve_encrypt_step_value :=
  intros k Hk;
  match goal with
  | Hlen : Zlength ?ol = ?i,
    Hprefix : forall k : Z, _ -> Znth k ?ol 0 = encrypt_char (Znth k ?l 0) |- _ =>
      destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
      [ rewrite app_Znth1 by lia;
        apply Hprefix;
        lia
      | assert (k = i) by lia;
        subst k;
        rewrite app_Znth2 by lia;
        replace (i - Zlength ol) with 0 by lia;
        rewrite Znth0_cons;
        rewrite_signed_encrypt;
        unfold encrypt_char;
        repeat rewrite app_Znth1 in * by lia;
        reflexivity ]
  end.

Ltac solve_encrypt_step :=
  encrypt_pre;
  match goal with
  | |- context[CharArray.full ?out (?i + 1) (app ?ol (cons ?v nil))] =>
      Exists (app ol (cons v nil))
  end;
  entailer!;
  [ solve_encrypt_step_value
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac solve_encrypt_init :=
  encrypt_pre;
  subst;
  Exists nil;
  match goal with
  | |- context[CharArray.undef_full ?p (Zlength ?l + 1)] =>
      sep_apply (CharArray.undef_full_split_to_undef_seg p 0 (Zlength l + 1));
      [ idtac | lia ];
      rewrite (CharArray.undef_seg_empty p 0);
      rewrite (CharArray.full_empty p 0)
  end;
  entailer!;
  lia.

Lemma proof_of_p089_encrypt_safety_wit_4 : p089_encrypt_safety_wit_4.
Proof. unfold p089_encrypt_safety_wit_4; intros; solve_encrypt_safety. Qed. 

Lemma proof_of_p089_encrypt_safety_wit_6 : p089_encrypt_safety_wit_6.
Proof. unfold p089_encrypt_safety_wit_6; intros; solve_encrypt_safety. Qed. 

Lemma proof_of_p089_encrypt_safety_wit_7 : p089_encrypt_safety_wit_7.
Proof. unfold p089_encrypt_safety_wit_7; intros; solve_encrypt_safety. Qed. 

Lemma proof_of_p089_encrypt_entail_wit_1 : p089_encrypt_entail_wit_1.
Proof. unfold p089_encrypt_entail_wit_1; intros; solve_encrypt_init. Qed. 

Lemma proof_of_p089_encrypt_entail_wit_2 : p089_encrypt_entail_wit_2.
Proof. unfold p089_encrypt_entail_wit_2; intros; solve_encrypt_step. Qed. 

Lemma proof_of_p089_encrypt_return_wit_1 : p089_encrypt_return_wit_1.
Proof.
  unfold p089_encrypt_return_wit_1.
  intros.
  pre_process.
  assert (i = len) by lia.
  subst i.
  Exists out_l_2.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  entailer!.
  - match goal with
    | Hlen : Zlength out_l_2 = len |- _ => rewrite Hlen
    end.
    entailer!.
  - eapply problem_89_spec_intro with (n := len); try lia; try assumption.
    intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = encrypt_char (Znth k l 0) |- _ =>
        apply Hprefix; lia
    end.
  - intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = encrypt_char (Znth k l 0) |- _ =>
        rewrite Hprefix by lia
    end.
    apply encrypt_char_nonzero.
    eapply lower_char_from_problem_89_pre; eauto; lia.
  - intros k Hk.
    pose proof (lower_char_from_problem_89_pre l k ltac:(assumption) ltac:(assumption) ltac:(lia)) as Hlower.
    unfold lower_char in Hlower.
    lia.
Qed. 
