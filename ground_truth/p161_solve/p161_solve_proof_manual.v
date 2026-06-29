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
From SimpleC.EE.CAV.ground_truth_p161_solve Require Import p161_solve_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p161_solve.
Local Open Scope sac.
Require Import Coq.NArith.BinNat.
From AUXLib Require Import ListLib.

Local Open Scope list_scope.

(* Proof helpers moved from p161_solve.v so public contract files expose definitions only. *)

Lemma contains_letter_list_app : forall a b,
  contains_letter_list (a ++ b) =
  orb (contains_letter_list a) (contains_letter_list b).
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. destruct (is_letter_zb x), (contains_letter_list xs); reflexivity.
Qed.
Lemma contains_letter_prefix_bool : forall i l,
  contains_letter_prefix i l = 0 \/ contains_letter_prefix i l = 1.
Proof.
  intros i l.
  unfold contains_letter_prefix.
  destruct (contains_letter_list (firstn (Z.to_nat i) l)); auto.
Qed.
Lemma contains_letter_bool : forall l,
  contains_letter l = 0 \/ contains_letter l = 1.
Proof.
  intros l.
  unfold contains_letter.
  destruct (contains_letter_list l); auto.
Qed.
Lemma flip_char_range : forall c,
  0 <= c <= 127 ->
  0 <= flip_char c <= 127.
Proof.
  unfold flip_char, is_lower_zb, is_upper_zb.
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
  unfold flip_char, is_lower_zb, is_upper_zb.
  intros c Hrange Hnz.
  repeat match goal with
  | |- context[Z.leb ?x ?y] =>
      destruct (Z.leb_spec x y); simpl
  end; lia.
Qed.
Lemma contains_letter_prefix_0 : forall l,
  contains_letter_prefix 0 l = 0.
Proof.
  reflexivity.
Qed.
Lemma firstn_succ_snoc_161 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = List.app (firstn n l) [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth_161 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  List.app (firstn (Z.to_nat i) l) [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_161 with (d := 0) by (rewrite Zlength_correct in H; lia).
  reflexivity.
Qed.
Lemma contains_letter_prefix_step : forall i l,
  0 <= i < Zlength l ->
  contains_letter_prefix (i + 1) l =
    if is_letter_zb (Znth i l 0)
    then 1
    else contains_letter_prefix i l.
Proof.
  intros i l Hi.
  unfold contains_letter_prefix.
  rewrite firstn_succ_Znth_161 by lia.
  rewrite contains_letter_list_app.
  simpl.
  destruct (contains_letter_list (firstn (Z.to_nat i) l));
    destruct (is_letter_zb (Znth i l 0)); reflexivity.
Qed.
Lemma contains_letter_prefix_full : forall l,
  contains_letter_prefix (Zlength l) l = contains_letter l.
Proof.
  intros l.
  unfold contains_letter_prefix, contains_letter.
  rewrite firstn_all2; [reflexivity |].
  rewrite Zlength_correct.
  lia.
Qed.
Lemma is_lower_alpha_ascii_of : forall c,
  0 <= c <= 127 ->
  is_lower_alpha (ascii_of c) = is_lower_zb c.
Proof.
  intros c Hc.
  unfold is_lower_alpha, is_lower_zb, ascii_of.
  unfold Ascii.leb, Ascii.compare.
  repeat rewrite <- N.leb_compare.
  change (N_of_ascii "a"%char) with 97%N.
  change (N_of_ascii "z"%char) with 122%N.
  assert (HN: N_of_ascii (ascii_of_nat (Z.to_nat c)) = N.of_nat (Z.to_nat c)).
  {
    apply Nnat.N2Nat.inj.
    rewrite Nnat.Nat2N.id.
    change (N.to_nat (N_of_ascii (ascii_of_nat (Z.to_nat c))))
      with (nat_of_ascii (ascii_of_nat (Z.to_nat c))).
    rewrite nat_ascii_embedding by lia.
    reflexivity.
  }
  rewrite HN.
  destruct (Z.leb_spec 97 c); destruct (Z.leb_spec c 122); simpl;
    repeat match goal with
    | |- context[(?a <=? ?b)%N] => destruct (N.leb_spec0 a b); simpl
    end; try reflexivity; lia.
Qed.
Lemma is_upper_alpha_ascii_of : forall c,
  0 <= c <= 127 ->
  is_upper_alpha (ascii_of c) = is_upper_zb c.
Proof.
  intros c Hc.
  unfold is_upper_alpha, is_upper_zb, ascii_of.
  unfold Ascii.leb, Ascii.compare.
  repeat rewrite <- N.leb_compare.
  change (N_of_ascii "A"%char) with 65%N.
  change (N_of_ascii "Z"%char) with 90%N.
  assert (HN: N_of_ascii (ascii_of_nat (Z.to_nat c)) = N.of_nat (Z.to_nat c)).
  {
    apply Nnat.N2Nat.inj.
    rewrite Nnat.Nat2N.id.
    change (N.to_nat (N_of_ascii (ascii_of_nat (Z.to_nat c))))
      with (nat_of_ascii (ascii_of_nat (Z.to_nat c))).
    rewrite nat_ascii_embedding by lia.
    reflexivity.
  }
  rewrite HN.
  destruct (Z.leb_spec 65 c); destruct (Z.leb_spec c 90); simpl;
    repeat match goal with
    | |- context[(?a <=? ?b)%N] => destruct (N.leb_spec0 a b); simpl
    end; try reflexivity; lia.
Qed.
Lemma is_letter_dec_ascii_of : forall c,
  0 <= c <= 127 ->
  is_letter_dec (ascii_of c) = is_letter_zb c.
Proof.
  intros c Hc.
  unfold is_letter_dec, is_letter_zb.
  rewrite is_lower_alpha_ascii_of by lia.
  rewrite is_upper_alpha_ascii_of by lia.
  reflexivity.
Qed.
Lemma change_case_ascii_of : forall c,
  0 <= c <= 127 ->
  change_case (ascii_of c) = ascii_of (flip_char c).
Proof.
  intros c Hc.
  unfold change_case, my_uppercase, my_lowercase, flip_char.
  rewrite is_lower_alpha_ascii_of by lia.
  rewrite is_upper_alpha_ascii_of by lia.
  destruct (is_lower_zb c) eqn:Hlow; simpl.
  - unfold ascii_of.
    rewrite nat_ascii_embedding by lia.
    unfold is_lower_zb in Hlow.
    apply andb_true_iff in Hlow as [H1 H2].
    apply Z.leb_le in H1; apply Z.leb_le in H2.
    replace (Z.to_nat (c - 32)) with (Z.to_nat c - 32)%nat by lia.
    reflexivity.
  - destruct (is_upper_zb c) eqn:Hup; simpl.
    + unfold ascii_of.
      rewrite nat_ascii_embedding by lia.
      unfold is_upper_zb in Hup.
      apply andb_true_iff in Hup as [H1 H2].
      apply Z.leb_le in H1; apply Z.leb_le in H2.
      replace (Z.to_nat (c + 32)) with (Z.to_nat c + 32)%nat by lia.
      reflexivity.
    + reflexivity.
Qed.
Lemma contains_letter_list_correct : forall l,
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127) ->
  contains_letter_dec (map ascii_of l) = contains_letter_list l.
Proof.
  induction l as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - rewrite is_letter_dec_ascii_of.
    + rewrite IH; [reflexivity |].
      intros i Hi.
      specialize (Hrange (i + 1)).
      simpl in Hrange.
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons; lia.
    + specialize (Hrange 0).
      simpl in Hrange.
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      split; [lia | rewrite Zlength_correct; simpl; lia].
Qed.
Lemma map_change_case_ascii_of : forall l,
  (forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0 <= 127) ->
  map change_case (map ascii_of l) = map ascii_of (map flip_char l).
Proof.
  induction l as [| c rest IH]; intros Hrange; simpl.
  - reflexivity.
  - rewrite change_case_ascii_of.
    + rewrite IH; [reflexivity |].
      intros i Hi.
      specialize (Hrange (i + 1)).
      simpl in Hrange.
      rewrite Znth_cons in Hrange by lia.
      replace (i + 1 - 1) with i in Hrange by lia.
      apply Hrange.
      rewrite Zlength_cons; lia.
    + specialize (Hrange 0).
      simpl in Hrange.
      rewrite Znth0_cons in Hrange.
      apply Hrange.
      split; [lia | rewrite Zlength_correct; simpl; lia].
Qed.
Lemma string_of_list_map_ascii : forall l,
  string_of_list l = string_of_list_ascii (map ascii_of l).
Proof.
  induction l; simpl; congruence.
Qed.
Lemma string_of_list_map_flip : forall l,
  ascii_range l ->
  string_of_list (map flip_char l) =
  string_of_list_ascii (map change_case (map ascii_of l)).
Proof.
  intros l Hrange.
  rewrite string_of_list_map_ascii.
  f_equal.
  symmetry.
  apply map_change_case_ascii_of; exact Hrange.
Qed.
Lemma map_flip_length : forall l,
  Zlength (map flip_char l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, map_length.
  reflexivity.
Qed.
Lemma list_eq_Znth_161 : forall (a b : list Z),
  Zlength a = Zlength b ->
  (forall k, 0 <= k < Zlength a -> Znth k a 0 = Znth k b 0) ->
  a = b.
Proof.
  induction a as [| x xs IH]; destruct b as [| y ys]; intros Hlen Hnth; simpl in *.
  - reflexivity.
  - repeat rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - repeat rewrite Zlength_correct in Hlen. simpl in Hlen. lia.
  - assert (Hx : x = y).
    {
      specialize (Hnth 0).
      repeat rewrite Znth0_cons in Hnth.
      apply Hnth.
      rewrite Zlength_correct. simpl. lia.
    }
    subst y.
    f_equal.
    apply IH.
    + repeat rewrite Zlength_correct in Hlen. simpl in Hlen.
      rewrite !Zlength_correct. lia.
    + intros k Hk.
      specialize (Hnth (k + 1)).
      repeat rewrite Znth_cons in Hnth by lia.
      replace (k + 1 - 1) with k in Hnth by lia.
      apply Hnth.
      rewrite Zlength_correct in *.
      simpl.
      lia.
Qed.
Lemma Znth_map_flip_161 : forall l k,
  0 <= k < Zlength l ->
  Znth k (map flip_char l) 0 = flip_char (Znth k l 0).
Proof.
  induction l as [| x xs IH]; intros k Hk.
  - rewrite Zlength_correct in Hk. simpl in Hk. lia.
  - destruct (Z.eq_dec k 0) as [-> | Hnz].
    + simpl. repeat rewrite Znth0_cons. reflexivity.
    + simpl.
      rewrite Znth_cons by lia.
      rewrite Znth_cons by lia.
      apply IH.
      rewrite Zlength_cons in Hk.
      lia.
Qed.
Lemma Zlength_rev_161 : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, rev_length.
  reflexivity.
Qed.
Lemma Znth_rev_161 : forall l k,
  0 <= k < Zlength l ->
  Znth k (rev l) 0 = Znth (Zlength l - 1 - k) l 0.
Proof.
  intros l k Hk.
  unfold Znth.
  rewrite rev_nth by (rewrite Zlength_correct in Hk; lia).
  f_equal.
  rewrite Zlength_correct in Hk |- *.
  lia.
Qed.
Lemma output_is_map_flip_161 : forall input output,
  Zlength output = Zlength input ->
  (forall k, 0 <= k < Zlength input ->
    Znth k output 0 = flip_char (Znth k input 0)) ->
  output = map flip_char input.
Proof.
  intros input output Hlen Hpoint.
  apply list_eq_Znth_161.
  - rewrite map_flip_length. exact Hlen.
  - intros k Hk.
    rewrite Hpoint by lia.
    rewrite Znth_map_flip_161 by lia.
    reflexivity.
Qed.
Lemma output_is_rev_161 : forall input output,
  Zlength output = Zlength input ->
  (forall k, 0 <= k < Zlength input ->
    Znth k output 0 = Znth (Zlength input - 1 - k) input 0) ->
  output = rev input.
Proof.
  intros input output Hlen Hpoint.
  apply list_eq_Znth_161.
  - rewrite Zlength_rev_161. exact Hlen.
  - intros k Hk.
    rewrite Hpoint by lia.
    rewrite Znth_rev_161 by lia.
    reflexivity.
Qed.
Lemma list_ascii_of_string_string_of_list_161 : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l; simpl; congruence.
Qed.
Lemma problem_161_spec_intro_flip : forall input output,
  ascii_range input ->
  contains_letter input = 1 ->
  output = map flip_char input ->
  problem_161_spec input output.
Proof.
  intros input output Hrange Hhas ->.
  unfold problem_161_spec, solve_impl.
  rewrite list_ascii_of_string_string_of_list_161.
  unfold contains_letter in Hhas.
  rewrite contains_letter_list_correct by exact Hrange.
  destruct (contains_letter_list input); [| discriminate].
  rewrite string_of_list_map_flip by exact Hrange.
  reflexivity.
Qed.
Lemma problem_161_spec_intro_rev : forall input output,
  ascii_range input ->
  contains_letter input = 0 ->
  output = rev input ->
  problem_161_spec input output.
Proof.
  intros input output Hrange Hhas ->.
  unfold problem_161_spec, solve_impl.
  rewrite list_ascii_of_string_string_of_list_161.
  unfold contains_letter in Hhas.
  rewrite contains_letter_list_correct by exact Hrange.
  destruct (contains_letter_list input); [discriminate |].
  rewrite string_of_list_map_ascii.
  rewrite map_rev.
  reflexivity.
Qed.


Ltac prep_161 :=
  pre_process;
  subst;
  repeat rewrite app_Znth1 in * by lia.

Ltac simp_letter_161 :=
  unfold is_letter_zb, is_lower_zb, is_upper_zb, flip_char;
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
  repeat rewrite Bool.orb_true_r;
  repeat rewrite Bool.orb_true_l;
  repeat rewrite Bool.orb_false_r;
  repeat rewrite Bool.orb_false_l;
  repeat rewrite Bool.andb_false_r;
  repeat rewrite Bool.andb_false_l;
  repeat rewrite Bool.andb_true_r;
  repeat rewrite Bool.andb_true_l;
  simpl.

Ltac rewrite_signed_input_161 :=
  repeat match goal with
  | Hrange : ascii_range ?lst |- context[signed_last_nbits (Znth ?idx ?lst 0) 8] =>
      let Hr := fresh "Hchar" in
      pose proof (Hrange idx ltac:(lia)) as Hr;
      rewrite (signed_last_nbits_eq (Znth idx lst 0) 8) by lia
  end.

Ltac choose_app_out_161 :=
  match goal with
  | |- context[CharArray.full _ _ (app ?ol (cons (signed_last_nbits (Znth (Zlength ?ol) ?inp 0) 8) nil))] =>
      Exists (app ol (cons (signed_last_nbits (Znth (Zlength ol) inp 0) 8) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (?n - 1 - Zlength ?ol) ?inp 0) nil))] =>
      Exists (app ol (cons (Znth (n - 1 - Zlength ol) inp 0) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0 - 32) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0 - 32) nil))
  | |- context[CharArray.full _ _ (app ?ol (cons (Znth (Zlength ?ol) ?inp 0 + 32) nil))] =>
      Exists (app ol (cons (Znth (Zlength ol) inp 0 + 32) nil))
  end.

Ltac solve_extend_flip_161 :=
  prep_161;
  choose_app_out_161;
  entailer!;
  [ intros k Hk;
    match goal with
    | Hprefix : forall x : Z, 0 <= x < Zlength ?ol -> _ |- _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          apply Hprefix; lia
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite_signed_input_161;
          cbv [flip_char is_lower_zb is_upper_zb];
          repeat match goal with
          | |- context[Z.leb ?x ?y] =>
              destruct (Z.leb_spec x y); simpl
          end; try reflexivity; lia ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac finish_extend_flip_161 :=
  entailer!;
  [ intros k Hk;
    match goal with
    | |- Znth k (?ol ++ _) 0 = _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          match goal with Hprefix : forall x : Z, _ -> _ |- _ => apply Hprefix; lia end
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite_signed_input_161;
          cbv [flip_char is_lower_zb is_upper_zb];
          repeat match goal with
          | |- context[Z.leb ?x ?y] =>
              destruct (Z.leb_spec x y); simpl
          end; try reflexivity; lia ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac solve_extend_rev_161 :=
  prep_161;
  choose_app_out_161;
  entailer!;
  [ intros k Hk;
    match goal with
    | Hlen : Zlength ?ol = ?i,
      Hprefix : forall x : Z, 0 <= x < Zlength ?ol -> _ |- _ =>
        destruct (Z_lt_ge_dec k i) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          apply Hprefix; lia
        | assert (k = i) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (i - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          rewrite app_Znth1 by lia;
          reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Ltac finish_extend_rev_161 :=
  entailer!;
  [ intros k Hk;
    match goal with
    | |- Znth k (?ol ++ _) 0 = _ =>
        destruct (Z_lt_ge_dec k (Zlength ol)) as [Hlt | Hge];
        [ rewrite app_Znth1 by lia;
          match goal with Hprefix : forall x : Z, _ -> _ |- _ => apply Hprefix; lia end
        | assert (k = Zlength ol) by lia; subst k;
          rewrite app_Znth2 by lia;
          replace (Zlength ol - Zlength ol) with 0 by lia;
          rewrite Znth0_cons;
          try rewrite app_Znth1 by lia;
          reflexivity ]
    end
  | rewrite Zlength_app, Zlength_cons, Zlength_nil; lia ].

Lemma proof_of_p161_solve_entail_wit_1 : p161_solve_entail_wit_1.
Proof.
  unfold p161_solve_entail_wit_1.
  intros.
  prep_161.
  entailer!.
Qed.

Lemma proof_of_p161_solve_entail_wit_2_1 : p161_solve_entail_wit_2_1.
Proof.
  unfold p161_solve_entail_wit_2_1.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_p161_solve_entail_wit_2_2 : p161_solve_entail_wit_2_2.
Proof.
  unfold p161_solve_entail_wit_2_2.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_p161_solve_entail_wit_2_3 : p161_solve_entail_wit_2_3.
Proof.
  unfold p161_solve_entail_wit_2_3.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_p161_solve_entail_wit_2_4 : p161_solve_entail_wit_2_4.
Proof.
  unfold p161_solve_entail_wit_2_4.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_p161_solve_entail_wit_2_5 : p161_solve_entail_wit_2_5.
Proof.
  unfold p161_solve_entail_wit_2_5.
  intros.
  prep_161.
  entailer!.
  rewrite contains_letter_prefix_step by lia.
  simp_letter_161.
  reflexivity.
Qed.

Lemma proof_of_p161_solve_entail_wit_3 : p161_solve_entail_wit_3.
Proof.
  unfold p161_solve_entail_wit_3.
  intros.
  prep_161.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg out 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty out 0).
  rewrite (CharArray.full_empty out 0).
  entailer!.
  - rewrite <- contains_letter_prefix_full.
    match goal with
    | H : 1 = contains_letter_prefix ?idx l |- _ =>
        replace (Zlength l) with idx by lia; exact H
    | H : contains_letter_prefix ?idx l = 1 |- _ =>
        replace (Zlength l) with idx by lia; symmetry; exact H
    end.
  - rewrite Zlength_correct; lia.
Qed.

Lemma proof_of_p161_solve_entail_wit_4_1 : p161_solve_entail_wit_4_1.
Proof.
  unfold p161_solve_entail_wit_4_1.
  intros.
  prep_161.
  Exists (out_l_2 ++ signed_last_nbits (Znth (Zlength out_l_2) l 0) 8 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
  Unshelve.
  all: try solve [rewrite Zlength_correct; lia | lia].
Qed.

Lemma proof_of_p161_solve_entail_wit_4_2 : p161_solve_entail_wit_4_2.
Proof.
  unfold p161_solve_entail_wit_4_2.
  intros.
  prep_161.
  Exists (out_l_2 ++ Znth (Zlength out_l_2) l 0 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_p161_solve_entail_wit_4_3 : p161_solve_entail_wit_4_3.
Proof.
  unfold p161_solve_entail_wit_4_3.
  intros.
  prep_161.
  Exists (out_l_2 ++ signed_last_nbits (Znth (Zlength out_l_2) l 0) 8 :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_p161_solve_entail_wit_4_4 : p161_solve_entail_wit_4_4.
Proof.
  unfold p161_solve_entail_wit_4_4.
  intros.
  prep_161.
  Exists (out_l_2 ++ (Znth (Zlength out_l_2) l 0 - 32) :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_p161_solve_entail_wit_4_5 : p161_solve_entail_wit_4_5.
Proof.
  unfold p161_solve_entail_wit_4_5.
  intros.
  prep_161.
  Exists (out_l_2 ++ (Znth (Zlength out_l_2) l 0 + 32) :: nil).
  finish_extend_flip_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_p161_solve_entail_wit_5 : p161_solve_entail_wit_5.
Proof.
  unfold p161_solve_entail_wit_5.
  intros.
  prep_161.
  Exists (@nil Z).
  sep_apply (CharArray.undef_full_split_to_undef_seg out 0 (Zlength l + 1)).
  rewrite (CharArray.undef_seg_empty out 0).
  rewrite (CharArray.full_empty out 0).
  entailer!.
  - try rewrite <- contains_letter_prefix_full.
    try match goal with
    | H : 0 = contains_letter_prefix ?idx l |- _ =>
        replace (Zlength l) with idx by lia; exact H
    | H : contains_letter_prefix ?idx l = 0 |- _ =>
        replace (Zlength l) with idx by lia; symmetry; exact H
    end.
    pose proof (contains_letter_prefix_bool i l); lia.
  - destruct (contains_letter_prefix_bool i l) as [Hz | Hz]; try lia.
    replace i with (Zlength l) by lia.
    rewrite contains_letter_prefix_full.
    reflexivity.
  - rewrite Zlength_correct; lia.
Qed.

Lemma proof_of_p161_solve_entail_wit_6 : p161_solve_entail_wit_6.
Proof.
  unfold p161_solve_entail_wit_6.
  intros.
  prep_161.
  Exists (out_l_2 ++ Znth (Zlength l - 1 - Zlength out_l_2) l 0 :: nil).
  finish_extend_rev_161.
  all: try solve [rewrite Zlength_app, Zlength_cons, Zlength_nil; lia | lia | reflexivity].
Qed.

Lemma proof_of_p161_solve_return_wit_1 : p161_solve_return_wit_1.
Proof.
  unfold p161_solve_return_wit_1.
  intros.
  prep_161.
  assert (Hout_len_eq : Zlength out_l_2 = Zlength l) by lia.
  Exists out_l_2.
  replace (Zlength out_l_2 + 1) with (Zlength l + 1) by lia.
  rewrite (CharArray.undef_seg_empty out (Zlength l + 1)).
  entailer!.
  - apply problem_161_spec_intro_rev; try assumption.
    + apply output_is_rev_161.
      * assumption.
      * intros k Hk.
        match goal with
        | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = Znth (Zlength l - 1 - k) l 0 |- _ =>
            apply Hprefix; lia
        end.
  - intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = Znth (Zlength l - 1 - k) l 0,
      Hnz : forall k : Z, _ -> Znth k l 0 <> 0 |- _ =>
        rewrite Hprefix by lia;
        apply Hnz; lia
    end.
Qed.

Lemma proof_of_p161_solve_return_wit_2 : p161_solve_return_wit_2.
Proof.
  unfold p161_solve_return_wit_2.
  intros.
  prep_161.
  assert (Hout_len_eq : Zlength out_l_2 = Zlength l) by lia.
  Exists out_l_2.
  replace (Zlength out_l_2 + 1) with (Zlength l + 1) by lia.
  rewrite (CharArray.undef_seg_empty out (Zlength l + 1)).
  entailer!.
  - apply problem_161_spec_intro_flip; try assumption.
    + apply output_is_map_flip_161.
      * assumption.
      * intros k Hk.
        match goal with
        | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char (Znth k l 0) |- _ =>
            apply Hprefix; lia
        end.
  - intros k Hk.
    match goal with
    | Hprefix : forall k : Z, _ -> Znth k out_l_2 0 = flip_char (Znth k l 0),
      Hrange : ascii_range l,
      Hnz : forall k : Z, _ -> Znth k l 0 <> 0 |- _ =>
        rewrite Hprefix by lia;
        apply flip_char_nonzero;
        [ apply Hrange; lia | apply Hnz; lia ]
    end.
Qed.
