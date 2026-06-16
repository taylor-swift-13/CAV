Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From Coq Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic IntLib.
From SimpleC.EE.QCP_demos_LLM Require Import p089_encrypt_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p089_encrypt.
Require Import string_bridge.
Local Open Scope sac.

(* ------------------------------------------------------------------ *)
(* Helper 1: list_ascii_of_string (string_of_list l) = map ascii_of l *)
(* ------------------------------------------------------------------ *)
Lemma list_ascii_of_string_of_list : forall (l : list Z),
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [| c rest IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Helper 2: From all_lowercase_ascii (string_of_list l) + ascii_range l,
   extract 97 <= Znth i l 0 <= 122 for 0 <= i < Zlength l            *)
(* ------------------------------------------------------------------ *)
Lemma all_lowercase_Znth : forall (l : list Z) (i : Z),
  0 <= i < Zlength l ->
  ascii_range l ->
  all_lowercase_ascii (string_of_list l) ->
  97 <= Znth i l 0 <= 122.
Proof.
  induction l as [| h t IH].
  - intros i Hi _ _. rewrite Zlength_nil in Hi. lia.
  - intros i Hi Hrange Hlow.
    rewrite Zlength_cons in Hi.
    simpl in Hlow.
    destruct Hlow as [Hhlow Htlow].
    unfold is_lowercase_ascii in Hhlow.
    assert (Hh_range : 0 <= h < 256).
    { specialize (Hrange 0).
      rewrite Znth0_cons in Hrange.
      apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
    assert (Hnat_h : (nat_of_ascii (ascii_of_nat (Z.to_nat h)) = Z.to_nat h)%nat).
    { apply nat_ascii_embedding. zify. lia. }
    unfold ascii_of in Hhlow.
    rewrite Hnat_h in Hhlow.
    change (nat_of_ascii "a") with 97%nat in Hhlow.
    change (nat_of_ascii "z") with 122%nat in Hhlow.
    assert (Hh : 97 <= h <= 122).
    { split; zify; lia. }
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. exact Hh.
    + rewrite Znth_cons by lia.
      apply IH.
      * lia.
      * intros k Hk.
        specialize (Hrange (k + 1)).
        rewrite Znth_cons in Hrange by lia.
        replace (k + 1 - 1) with k in Hrange by lia.
        apply Hrange. rewrite Zlength_cons. lia.
      * exact Htlow.
Qed.

(* ------------------------------------------------------------------ *)
(* Helper 3: char_relation (ascii_of c) (ascii_of (encrypt_char c))
   holds for every lowercase c in [97, 122]                           *)
(* ------------------------------------------------------------------ *)
Lemma char_relation_encrypt_char : forall c,
  97 <= c <= 122 ->
  char_relation (ascii_of c) (ascii_of (encrypt_char c)).
Proof.
  intros c Hc.
  unfold encrypt_char, ascii_of.
  interval_cases c; compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Helper 4: Lift pointwise encrypt property to problem_89_spec        *)
(* ------------------------------------------------------------------ *)
Lemma problem_89_spec_from_encrypt : forall (l out_l : list Z),
  problem_89_pre l ->
  ascii_range l ->
  Zlength l = Zlength out_l ->
  (forall k, 0 <= k < Zlength l -> Znth k out_l 0 = encrypt_char (Znth k l 0)) ->
  problem_89_spec l out_l.
Proof.
  unfold problem_89_spec, problem_89_pre.
  induction l as [| h t IH]; intros out_l Hlow Hrange Hlen Henc.
  - rewrite Zlength_nil in Hlen.
    destruct out_l as [| h' t'].
    + simpl. constructor.
    + rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg t'). lia.
  - destruct out_l as [| h' t'].
    { rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg t). lia. }
    simpl string_of_list.
    simpl list_ascii_of_string.
    constructor.
    + (* char_relation (ascii_of h) (ascii_of h') *)
      assert (Hh' : h' = encrypt_char h).
      { specialize (Henc 0).
        rewrite Znth0_cons in Henc.
        rewrite Znth0_cons in Henc.
        apply Henc. rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia. }
      rewrite Hh'.
      apply char_relation_encrypt_char.
      apply (all_lowercase_Znth (h :: t) 0).
      * rewrite Zlength_cons. pose proof (Zlength_nonneg t). lia.
      * exact Hrange.
      * exact Hlow.
    + (* Forall2 char_relation ... tail *)
      apply IH.
      * (* problem_89_pre t *)
        simpl in Hlow. exact (proj2 Hlow).
      * (* ascii_range t *)
        intros k Hk.
        specialize (Hrange (k + 1)).
        rewrite Znth_cons in Hrange by lia.
        replace (k + 1 - 1) with k in Hrange by lia.
        apply Hrange. rewrite Zlength_cons. lia.
      * (* Zlength t = Zlength t' *)
        rewrite Zlength_cons in Hlen. rewrite Zlength_cons in Hlen. lia.
      * (* forall k, Znth k t' 0 = encrypt_char (Znth k t 0) *)
        intros k Hk.
        specialize (Henc (k + 1)).
        rewrite Znth_cons in Henc by lia.
        replace (k + 1 - 1) with k in Henc by lia.
        rewrite Znth_cons in Henc by lia.
        replace (k + 1 - 1) with k in Henc by lia.
        apply Henc. rewrite Zlength_cons. lia.
Qed.

(* ================================================================== *)
(*  safety_wit_4: INT bounds for ((Znth i (app l [0]) 0 + 4 - 97) % 26 + 97) *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_safety_wit_4 : p089_encrypt_safety_wit_4.
Proof.
  pre_process.
  pose proof (Z.rem_bound_abs (Znth i (app l (cons 0 nil)) 0 + 4 - 97) 26 ltac:(lia)) as Hrem.
  rewrite Z.abs_lt in Hrem.
  split_pures.
  - dump_pre_spatial. lia.
  - dump_pre_spatial. lia.
Qed.

(* ================================================================== *)
(*  safety_wit_6: INT bounds for (Znth i (app l [0]) 0 + 4 - 97)     *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_safety_wit_6 : p089_encrypt_safety_wit_6.
Proof.
  pre_process.
  specialize (H5 i).
  rewrite app_Znth1 in H5 by lia.
  apply H5 in H3 as Hrange.
  split_pures.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia. lia.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia. lia.
Qed.

(* ================================================================== *)
(*  safety_wit_7: INT bounds for (Znth i (app l [0]) 0 + 4)           *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_safety_wit_7 : p089_encrypt_safety_wit_7.
Proof.
  pre_process.
  specialize (H5 i).
  rewrite app_Znth1 in H5 by lia.
  apply H5 in H3 as Hrange.
  split_pures.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia. lia.
  - dump_pre_spatial.
    rewrite app_Znth1 by lia. lia.
Qed.

(* ================================================================== *)
(*  entail_wit_1: Loop initialization with out_l_i = []               *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_entail_wit_1 : p089_encrypt_entail_wit_1.
Proof.
  pre_process.
  Exists (@nil Z).
  sep_apply CharArray.undef_full_to_undef_seg.
  rewrite (CharArray.full_empty retval 0).
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
    cancel (CharArray.undef_seg retval 0 (len + 1)).
  - split_pures.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. rewrite Zlength_nil. lia.
    + dump_pre_spatial. exact H4.
    + dump_pre_spatial. exact H5.
    + dump_pre_spatial. exact H3.
    + dump_pre_spatial. intros k [Hk1 Hk2]. lia.
    + dump_pre_spatial. intros k [Hk1 Hk2]. lia.
Qed.

(* ================================================================== *)
(*  entail_wit_2: Loop step                                            *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_entail_wit_2 : p089_encrypt_entail_wit_2.
Proof.
  pre_process.
  Exists (app out_l_i_2 (cons (signed_last_nbits
    ((((Znth i (app l (cons 0 nil)) 0) + 4) - 97) % 26 + 97) 8) nil)).
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
    cancel (CharArray.full out (i + 1) (app out_l_i_2 (cons (signed_last_nbits
      ((((Znth i (app l (cons 0 nil)) 0) + 4) - 97) % 26 + 97) 8) nil))).
    cancel (CharArray.undef_seg out (i + 1) (len + 1)).
  - (* Pure goals *)
    split_pures.
    + (* 0 <= i + 1 *)
      dump_pre_spatial. lia.
    + (* i + 1 <= len *)
      dump_pre_spatial. lia.
    + (* Zlength (out_l_i_2 ++ [v]) = i + 1 *)
      dump_pre_spatial.
      rewrite Zlength_app. rewrite H3. simpl. lia.
    + (* problem_89_pre l *)
      dump_pre_spatial. exact H4.
    + (* ascii_range l *)
      dump_pre_spatial. exact H5.
    + (* forall k, 0<=k/\k<len -> Znth k l 0 <> 0 *)
      dump_pre_spatial. exact H6.
    + (* forall k_2, 0<=k_2/\k_2<i+1 -> Znth k_2 (app out_l_i_2 [v]) 0 = encrypt_char (Znth k_2 l 0) *)
      dump_pre_spatial.
      intros k_2 [Hk2a Hk2b].
      assert (Hil : i < Zlength l) by lia.
      destruct (Z_lt_ge_dec k_2 i) as [Hlt | Hge].
      * (* k_2 < i: use prior invariant *)
        rewrite app_Znth1 by lia.
        apply H7. split; lia.
      * (* k_2 = i *)
        assert (k_2 = i) by lia. subst k_2.
        rewrite app_Znth2 by lia.
        rewrite H3. rewrite Z.sub_diag. simpl.
        (* Need: signed_last_nbits (...) 8 = encrypt_char (Znth i l 0) *)
        rewrite app_Znth1 by lia.
        (* Value w = (Znth i l 0 + 4 - 97) % 26 + 97 *)
        (* signed_last_nbits w 8 = w since w in [72, 123) ⊂ [-128, 128) *)
        set (w := (Znth i l 0 + 4 - 97) % 26 + 97).
        assert (Hw_range : -128 <= w < 128).
        {
          unfold w.
          pose proof (Z.rem_bound_abs (Znth i l 0 + 4 - 97) 26 ltac:(lia)) as Habs.
          rewrite Z.abs_lt in Habs.
          specialize (H5 i ltac:(lia)).
          rewrite app_Znth1 in H5 by lia.
          lia.
        }
        rewrite (signed_last_nbits_eq w 8 ltac:(lia) Hw_range).
        unfold w, encrypt_char.
        reflexivity.
    + (* forall k_3, 0<=k_3/\k_3<i+1 -> Znth k_3 (app out_l_i_2 [v]) 0 <> 0 *)
      dump_pre_spatial.
      intros k_3 [Hk3a Hk3b].
      destruct (Z_lt_ge_dec k_3 i) as [Hlt | Hge].
      * (* k_3 < i: from prior nonzero invariant *)
        rewrite app_Znth1 by lia.
        apply H8. split; lia.
      * (* k_3 = i *)
        assert (k_3 = i) by lia. subst k_3.
        rewrite app_Znth2 by lia.
        rewrite H3. rewrite Z.sub_diag. simpl.
        set (w := (Znth i l 0 + 4 - 97) % 26 + 97).
        assert (Hw_range : -128 <= w < 128).
        {
          unfold w.
          pose proof (Z.rem_bound_abs (Znth i l 0 + 4 - 97) 26 ltac:(lia)) as Habs.
          rewrite Z.abs_lt in Habs.
          specialize (H5 i ltac:(lia)).
          rewrite app_Znth1 in H5 by lia.
          lia.
        }
        rewrite (signed_last_nbits_eq w 8 ltac:(lia) Hw_range).
        unfold w.
        pose proof (Z.rem_bound_abs (Znth i l 0 + 4 - 97) 26 ltac:(lia)) as Habs.
        rewrite Z.abs_lt in Habs.
        specialize (H5 i ltac:(lia)).
        rewrite app_Znth1 in H5 by lia.
        lia.
Qed.

(* ================================================================== *)
(*  return_wit_1: Return postcondition                                  *)
(* ================================================================== *)
Lemma proof_of_p089_encrypt_return_wit_1 : p089_encrypt_return_wit_1.
Proof.
  pre_process.
  assert (Hi_eq : i = len) by lia.
  subst i.
  Exists out_l_i.
  rewrite (CharArray.undef_seg_empty out (len + 1)).
  split_pure_spatial.
  - cancel (CharArray.full s_pre (len + 1) (app l (cons 0 nil))).
    cancel (CharArray.full out (len + 1) (app out_l_i (cons 0 nil))).
  - split_pures.
    + (* forall k, 0<=k/\k<len -> Znth k l 0 <> 0 *)
      dump_pre_spatial. exact H6.
    + (* forall k_2, 0<=k_2/\k_2<len -> Znth k_2 out_l_i 0 <> 0 *)
      dump_pre_spatial.
      intros k_2 [Hk2a Hk2b].
      apply H8. split; lia.
    + (* Zlength out_l_i = len *)
      dump_pre_spatial. lia.
    + (* problem_89_spec l out_l_i *)
      dump_pre_spatial.
      apply problem_89_spec_from_encrypt.
      * exact H4.
      * exact H5.
      * lia.
      * intros k Hk. apply H7. split; lia.
Qed.
