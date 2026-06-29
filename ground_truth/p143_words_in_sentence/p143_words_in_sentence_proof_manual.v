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
From SimpleC.EE.CAV.ground_truth_p143_words_in_sentence Require Import p143_words_in_sentence_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.

Import naive_C_Rules.
Require Import p143_words_in_sentence.
Local Open Scope sac.
Require Import Coq.Arith.PeanoNat.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope list_scope.

(* Proof helpers moved from p143_words_in_sentence.v so public contract files expose definitions only. *)

Lemma split_words_z_aux_app_space : forall cur rest,
  split_words_z_aux cur (rest ++ [32]) =
  split_words_z_aux cur rest.
Proof.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur; simpl; reflexivity.
  - destruct (Z.eqb h 32); destruct cur; simpl; rewrite ?IH; try reflexivity.
Qed.
Lemma split_words_z_app_space : forall sentence,
  split_words (sentence ++ [32]) = split_words sentence.
Proof.
  intros sentence.
  unfold split_words.
  apply split_words_z_aux_app_space.
Qed.
Lemma words_in_sentence_output_app_space : forall sentence,
  words_in_sentence_output (sentence ++ [32]) =
  words_in_sentence_output sentence.
Proof.
  intros sentence.
  unfold words_in_sentence_output, selected_words.
  rewrite split_words_z_app_space.
  reflexivity.
Qed.
Lemma words_in_sentence_prefix_skip_space : forall sentence i,
  0 <= i < Zlength sentence ->
  Znth i (sentence ++ [0]) 0 = 32 ->
  words_in_sentence_prefix (i + 1) sentence =
  words_in_sentence_prefix i sentence.
Proof.
  intros sentence i Hi Hspace.
  unfold words_in_sentence_prefix.
  assert (sublist 0 (i + 1) sentence = sublist 0 i sentence ++ [32]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i sentence);
      [| lia | lia].
    rewrite (sublist_single 0 i sentence) by lia.
    rewrite app_Znth1 in Hspace by lia.
    rewrite Hspace.
    reflexivity.
  }
  rewrite Hsub.
  apply words_in_sentence_output_app_space.
Qed.
Lemma word_chars_empty : forall sentence start,
  word_chars sentence start start.
Proof.
  unfold word_chars.
  intros sentence start p Hp.
  lia.
Qed.
Lemma word_chars_step : forall sentence start i,
  word_chars sentence start i ->
  Znth i (sentence ++ [0]) 0 <> 32 ->
  word_chars sentence start (i + 1).
Proof.
  unfold word_chars.
  intros sentence start i Hchars Hi p Hp.
  assert (p < i \/ p = i) as [Hlt | ->] by lia.
  - apply Hchars. lia.
  - exact Hi.
Qed.
Lemma scan_ready_0 : forall sentence len,
  scan_ready sentence len 0.
Proof.
  unfold scan_ready.
  auto.
Qed.
Lemma scan_ready_at_end : forall sentence len i,
  i = len ->
  scan_ready sentence len i.
Proof.
  unfold scan_ready.
  auto.
Qed.
Lemma scan_ready_at_space : forall sentence len i,
  Znth i (sentence ++ [0]) 0 = 32 ->
  scan_ready sentence len i.
Proof.
  unfold scan_ready.
  auto.
Qed.
Lemma scan_ready_step_space : forall sentence len i,
  scan_ready sentence len i ->
  Znth i (sentence ++ [0]) 0 = 32 ->
  scan_ready sentence len (i + 1).
Proof.
  unfold scan_ready.
  intros sentence len i _ Hspace.
  right; right; right.
  replace (i + 1 - 1) with i by lia.
  exact Hspace.
Qed.
Lemma scan_ready_nonspace_start : forall sentence len i,
  scan_ready sentence len i ->
  i < len ->
  Znth i (sentence ++ [0]) 0 <> 32 ->
  word_start sentence i.
Proof.
  unfold scan_ready, word_start.
  intros sentence len i [Hzero | [Hend | [Hspace | Hprev]]] Hlt Hnonspace.
  - left. exact Hzero.
  - lia.
  - contradiction.
  - right. exact Hprev.
Qed.
Lemma word_copy_prefix_step : forall sentence start k,
  0 <= start ->
  0 <= k ->
  start + k < Zlength sentence ->
  word_copy_prefix start (k + 1) sentence =
  word_copy_prefix start k sentence ++
  [Znth (start + k) (sentence ++ [0]) 0].
Proof.
  intros sentence start k Hstart Hk Hbound.
  unfold word_copy_prefix.
  rewrite <- app_assoc.
  f_equal.
  replace (start + (k + 1)) with (start + k + 1) by lia.
  assert (0 <= start <= start + k) as Hlo by lia.
  assert (start + k <= start + k + 1 <= Zlength sentence) as Hhi by lia.
  rewrite (sublist_split start (start + k + 1) (start + k) sentence Hlo Hhi).
  rewrite (sublist_single 0 (start + k) sentence) by lia.
  rewrite app_Znth1 by lia.
  rewrite app_assoc.
  reflexivity.
Qed.
Lemma word_copy_prefix_0_nonempty : forall sentence start,
  Zlength (words_in_sentence_prefix start sentence) > 0 ->
  word_copy_prefix start 0 sentence =
  words_in_sentence_prefix start sentence ++ [32].
Proof.
  intros sentence start Hlen.
  unfold word_copy_prefix.
  destruct (Z.eqb_spec (Zlength (words_in_sentence_prefix start sentence)) 0) as [Heq | Hneq].
  - lia.
  - simpl.
  rewrite Zsublist_nil by lia.
  reflexivity.
Qed.
Lemma word_copy_prefix_0_empty : forall sentence start,
  Zlength (words_in_sentence_prefix start sentence) <= 0 ->
  word_copy_prefix start 0 sentence =
  words_in_sentence_prefix start sentence.
Proof.
  intros sentence start Hlen.
  assert (Zlength (words_in_sentence_prefix start sentence) = 0).
  { pose proof Zlength_nonneg (words_in_sentence_prefix start sentence). lia. }
  unfold word_copy_prefix.
  rewrite H.
  simpl.
  rewrite Zsublist_nil by lia.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma has_divisor_from_true_iff : forall n d,
  has_divisor_from n d = true <->
    exists x, (2 <= x <= d)%nat /\ (n mod x = 0)%nat.
Proof.
  intros n d.
  induction d as [| d IH].
  - cbn [has_divisor_from]. split; [discriminate | intros [x [[Hle Hle'] _]]; lia].
  - destruct d as [| d].
    + cbn [has_divisor_from]. split; [discriminate | intros [x [[Hle Hle'] _]]; lia].
    + cbn [has_divisor_from].
      destruct ((n mod S (S d)) =? 0)%nat eqn:Hmod.
      * split.
        { intro Htrue. exists (S (S d)). split; [lia | apply Nat.eqb_eq; exact Hmod]. }
        { intro Hexists. reflexivity. }
      * rewrite IH.
        split.
        { intros [x [[Hlo Hhi] Hx]].
          exists x. split; [lia | exact Hx]. }
        { intros [x [[Hlo Hhi] Hx]].
          assert (x = S (S d) \/ x <= S d)%nat as [-> | Hlt] by lia.
          - rewrite Hx in Hmod. discriminate.
          - exists x. split; [lia | exact Hx]. }
Qed.
Lemma prime_len_flag_composite : forall n,
  2 <= n ->
  (exists d, 2 <= d < n /\ Z.rem n d = 0) ->
  prime_len_flag n = 0.
Proof.
  intros n Hn [d [[Hdlo Hdhi] Hrem]].
  unfold prime_len_flag, is_prime_bool.
  remember (Z.to_nat n) as m eqn:Hm.
  destruct m as [| [| m]]; [lia | lia |].
  change ((if negb (has_divisor_from (S (S m)) (S m)) then 1 else 0) = 0).
  assert (has_divisor_from (S (S m)) (S m) = true) as Hdiv.
  { apply has_divisor_from_true_iff.
    exists (Z.to_nat d).
    split.
    - lia.
    - rewrite <- Nat2Z.inj_iff.
      rewrite Nat2Z.inj_mod.
      rewrite Hm.
      rewrite !Z2Nat.id by lia.
      rewrite Z.rem_mod_nonneg in Hrem by lia.
      exact Hrem. }
  rewrite Hdiv.
  reflexivity.
Qed.
Lemma prime_len_flag_prime : forall n,
  2 <= n ->
  (forall d, 2 <= d < n -> Z.rem n d <> 0) ->
  prime_len_flag n = 1.
Proof.
  intros n Hn Hnodiv.
  unfold prime_len_flag, is_prime_bool.
  remember (Z.to_nat n) as m eqn:Hm.
  destruct m as [| [| m]]; [lia | lia |].
  change ((if negb (has_divisor_from (S (S m)) (S m)) then 1 else 0) = 1).
  destruct (has_divisor_from (S (S m)) (S m)) eqn:Hdiv; [| reflexivity].
  apply has_divisor_from_true_iff in Hdiv.
  destruct Hdiv as [x [[Hxlo Hxhi] Hmod]].
  specialize (Hnodiv (Z.of_nat x)).
  assert (2 <= Z.of_nat x < n) by lia.
  specialize (Hnodiv H).
  rewrite <- Nat2Z.inj_iff in Hmod.
  rewrite Nat2Z.inj_mod in Hmod.
  rewrite Hm in Hmod.
  rewrite Z2Nat.id in Hmod by lia.
  rewrite Z.rem_mod_nonneg in Hnodiv by lia.
  contradiction.
Qed.
Lemma prime_loop_state_flag_0 : forall n j,
  2 <= n ->
  n <= j ->
  j <= n ->
  prime_loop_state n j 1 ->
  prime_len_flag n = 0.
Proof.
  intros n j Hn Hjn Hjn' Hstate.
  apply prime_len_flag_composite; [exact Hn |].
  unfold prime_loop_state in Hstate.
  destruct Hstate as [Hto _].
  destruct (Hto eq_refl) as [d [[Hdlo Hdj] Hrem]].
  exists d. split; [lia | exact Hrem].
Qed.
Lemma prime_loop_state_flag_1 : forall n j,
  2 <= n ->
  n <= j ->
  j <= n ->
  prime_loop_state n j 0 ->
  prime_len_flag n = 1.
Proof.
  intros n j Hn Hjn Hjn' Hstate.
  apply prime_len_flag_prime; [exact Hn |].
  intros d Hd.
  unfold prime_loop_state in Hstate.
  destruct Hstate as [_ Hfrom].
  intro Hrem.
  assert (0 = 1) by (apply Hfrom; exists d; split; [lia | exact Hrem]).
  discriminate.
Qed.
Lemma words_in_sentence_prefix_0 : forall sentence,
  words_in_sentence_prefix 0 sentence = [].
Proof.
  intros sentence.
  unfold words_in_sentence_prefix.
  unfold sublist.
  simpl.
  simpl.
  reflexivity.
Qed.
Lemma split_words_z_aux_no_space : forall cur w,
  nonspace_z_list w ->
  split_words_z_aux cur w =
  match rev cur ++ w with
  | [] => []
  | word => [word]
  end.
Proof.
  intros cur w Hno.
  revert cur Hno.
  induction w as [| h t IH]; intros cur Hno; simpl.
  - destruct cur as [| z cur]; simpl.
    + reflexivity.
    + rewrite app_nil_r. destruct (rev cur); reflexivity.
  - assert (h <> 32) as Hh by (apply Hno; simpl; auto).
    destruct (Z.eqb_spec h 32) as [Heq | Hneq]; [contradiction |].
    rewrite IH.
    + simpl.
      rewrite <- app_assoc.
      reflexivity.
    + intros x Hx. apply Hno. simpl; auto.
Qed.
Lemma split_words_z_aux_app_space_word : forall cur s w,
  nonspace_z_list w ->
  split_words_z_aux cur (s ++ [32] ++ w) =
  split_words_z_aux cur s ++ split_words_z_aux [] w.
Proof.
  intros cur s w Hno.
  revert cur.
  induction s as [| h t IH]; intros cur; simpl.
  - destruct cur as [| z cur]; simpl.
    + reflexivity.
    + reflexivity.
  - destruct (Z.eqb h 32); destruct cur as [| z cur]; simpl; rewrite IH; reflexivity.
Qed.
Lemma sublist_word_no_space : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_chars sentence start i ->
  nonspace_z_list (sublist start i sentence).
Proof.
  unfold nonspace_z_list, word_chars.
  intros sentence start i Hbounds Hi Hchars x Hin Hx.
  destruct (In_nth (sublist start i sentence) x 0 Hin) as [n [Hn Hnth]].
  assert (0 <= Z.of_nat n < Zlength (sublist start i sentence)) as Hnz.
  { rewrite Zlength_correct. lia. }
  assert (x = Znth (Z.of_nat n) (sublist start i sentence) 0) as Hxnth.
  {
    unfold Znth.
    rewrite Nat2Z.id.
    symmetry. exact Hnth.
  }
  rewrite Hxnth in Hx.
  rewrite Znth_sublist in Hx;
    [| lia | rewrite Zlength_sublist in Hnz by lia; lia].
  assert (start + Z.of_nat n < Zlength sentence) as Hlt.
  {
    rewrite Zlength_sublist in Hnz by lia.
    lia.
  }
  assert (start <= start + Z.of_nat n < i) as Hp.
  {
    rewrite Zlength_sublist in Hnz by lia.
    lia.
  }
  assert (Znth (start + Z.of_nat n) (sentence ++ [0]) 0 <> 32) as Hneq.
  { apply Hchars. exact Hp. }
  rewrite app_Znth1 in Hneq by lia.
  apply Hneq.
  replace (start + Z.of_nat n) with (Z.of_nat n + start) by lia.
  exact Hx.
Qed.
Lemma sublist_word_start_space : forall sentence start,
  0 < start ->
  start <= Zlength sentence ->
  word_start sentence start ->
  sublist 0 start sentence = sublist 0 (start - 1) sentence ++ [32].
Proof.
  intros sentence start Hpos Hbound Hstart.
  unfold word_start in Hstart.
  destruct Hstart as [Hzero | Hspace]; [lia |].
  rewrite (sublist_split 0 start (start - 1) sentence);
    [| lia | lia].
  assert (sublist (start - 1) start sentence = [Znth (start - 1) sentence 0]) as Hsingle.
  {
    pose proof (sublist_single 0 (start - 1) sentence) as Hs.
    specialize (Hs ltac:(lia)).
    replace (start - 1 + 1) with start in Hs by lia.
    exact Hs.
  }
  rewrite Hsingle.
  rewrite app_Znth1 in Hspace by lia.
  rewrite Hspace.
  reflexivity.
Qed.
Lemma split_words_z_boundary_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start sentence start ->
  word_chars sentence start i ->
  split_words (sublist 0 i sentence) =
  split_words (sublist 0 start sentence) ++
  split_words (sublist start i sentence).
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  rewrite (sublist_split 0 i start sentence);
    [| lia | lia].
  destruct (Z.eq_dec start 0) as [-> | Hnz].
  - rewrite Zsublist_nil by lia.
    simpl.
    reflexivity.
  - assert (0 < start) by lia.
    rewrite (sublist_word_start_space sentence start) by lia || exact Hstart.
    unfold split_words.
    rewrite <- app_assoc.
    rewrite split_words_z_aux_app_space_word by exact Hno.
    rewrite split_words_z_aux_app_space.
    reflexivity.
Qed.
Lemma selected_words_boundary_nonprime : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start sentence start ->
  word_chars sentence start i ->
  prime_len_flag (i - start) <> 1 ->
  selected_words (sublist 0 i sentence) =
  selected_words (sublist 0 start sentence).
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hnonprime.
  unfold selected_words.
  rewrite (split_words_z_boundary_word sentence start i) by assumption.
  rewrite List.filter_app.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  replace (split_words (sublist start i sentence)) with
    (match sublist start i sentence with [] => [] | word => [word] end).
  2:{
    unfold split_words.
    rewrite split_words_z_aux_no_space with (cur := []) by exact Hno.
    reflexivity.
  }
  destruct (sublist start i sentence) as [| h t] eqn:Hword.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl.
    assert (Zlength (h :: t) = i - start) as Hlen.
    {
      rewrite <- Hword.
      rewrite Zlength_sublist by lia.
      reflexivity.
    }
    rewrite Hlen.
    destruct (Z.eqb_spec (prime_len_flag (i - start)) 1); [contradiction |].
    simpl. rewrite app_nil_r. reflexivity.
Qed.
Lemma prime_len_flag_one_nonempty : forall w : list Z,
  Z.eqb (prime_len_flag (Zlength w)) 1 = true ->
  w <> [].
Proof.
  intros w Hprime ->.
  unfold prime_len_flag in Hprime.
  simpl in Hprime.
  discriminate.
Qed.
Lemma selected_words_nonempty : forall words w,
  In w (List.filter (fun w : list Z => Z.eqb (prime_len_flag (Zlength w)) 1) words) ->
  w <> [].
Proof.
  intros words w Hin.
  apply List.filter_In in Hin.
  destruct Hin as [_ Hprime].
  apply prime_len_flag_one_nonempty.
  exact Hprime.
Qed.
Lemma join_words_nonempty : forall ws,
  (forall w, In w ws -> w <> []) ->
  ws <> [] ->
  Zlength (join_words ws) > 0.
Proof.
  intros ws Hnonempty Hws.
  destruct ws as [| w rest]; [contradiction |].
  specialize (Hnonempty w ltac:(simpl; auto)).
  destruct w as [| h t]; [contradiction |].
  destruct rest as [| r rs]; simpl; rewrite Zlength_correct; simpl; lia.
Qed.
Lemma join_words_app_single : forall ws w,
  (forall word, In word ws -> word <> []) ->
  w <> [] ->
  join_words (ws ++ [w]) =
  join_words ws ++
  (if Z.eqb (Zlength (join_words ws)) 0 then [] else [32]) ++ w.
Proof.
  intros ws w Hws Hw.
  destruct ws as [| a rest].
  - simpl. reflexivity.
  - assert (Zlength (join_words (a :: rest)) > 0) as Hlen.
    {
      apply join_words_nonempty.
      - intros word Hin. apply Hws. simpl; auto.
      - discriminate.
    }
    destruct (Z.eqb_spec (Zlength (join_words (a :: rest))) 0) as [Hz | Hnz]; [lia |].
    clear Hlen Hnz.
    revert a Hws.
    induction rest as [| b rest IH]; intros a Hws; simpl.
    + reflexivity.
    + change (a ++ [32] ++ join_words ((b :: rest) ++ [w]) =
              (a ++ [32] ++ join_words (b :: rest)) ++ [32] ++ w).
      rewrite IH.
      * rewrite !app_assoc. reflexivity.
      * intros word Hin. apply Hws. simpl; auto.
Qed.
Lemma selected_words_boundary_prime : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start sentence start ->
  word_chars sentence start i ->
  prime_len_flag (i - start) = 1 ->
  selected_words (sublist 0 i sentence) =
  selected_words (sublist 0 start sentence) ++ [sublist start i sentence].
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hprime.
  unfold selected_words.
  rewrite (split_words_z_boundary_word sentence start i) by assumption.
  rewrite List.filter_app.
  assert (Hno := sublist_word_no_space sentence start i Hbounds Hi Hchars).
  replace (split_words (sublist start i sentence)) with
    (match sublist start i sentence with [] => [] | word => [word] end).
  2:{
    unfold split_words.
    rewrite split_words_z_aux_no_space with (cur := []) by exact Hno.
    reflexivity.
  }
  destruct (sublist start i sentence) as [| h t] eqn:Hword.
  - assert (i - start = 0) as Hlen0.
    {
      assert (0 <= start <= i /\ i <= Zlength sentence) as Hb by lia.
      pose proof (Zlength_sublist start i sentence Hb) as Hlen.
      rewrite Hword in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    }
    rewrite Hlen0 in Hprime.
    unfold prime_len_flag in Hprime.
    simpl in Hprime.
    discriminate.
  - simpl.
    assert (Zlength (h :: t) = i - start) as Hlen.
    {
      rewrite <- Hword.
      rewrite Zlength_sublist by lia.
      reflexivity.
    }
    rewrite Hlen, Hprime.
    simpl.
    reflexivity.
Qed.
Lemma words_in_sentence_prefix_nonprime_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start sentence start ->
  word_chars sentence start i ->
  prime_len_flag (i - start) <> 1 ->
  words_in_sentence_prefix i sentence =
  words_in_sentence_prefix start sentence.
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hnonprime.
  unfold words_in_sentence_prefix, words_in_sentence_output.
  rewrite (selected_words_boundary_nonprime sentence start i) by assumption.
  reflexivity.
Qed.
Lemma words_in_sentence_prefix_prime_word : forall sentence start i,
  0 <= start <= i ->
  i <= Zlength sentence ->
  word_start sentence start ->
  word_chars sentence start i ->
  prime_len_flag (i - start) = 1 ->
  words_in_sentence_prefix i sentence =
  word_copy_prefix start (i - start) sentence.
Proof.
  intros sentence start i Hbounds Hi Hstart Hchars Hprime.
  unfold words_in_sentence_prefix, words_in_sentence_output, word_copy_prefix.
  rewrite (selected_words_boundary_prime sentence start i) by assumption.
  assert (Hseg_nonempty : sublist start i sentence <> []).
  {
    intro Hnil.
    assert (i - start = 0) as Hlen0.
    {
      assert (0 <= start <= i /\ i <= Zlength sentence) as Hb by lia.
      pose proof (Zlength_sublist start i sentence Hb) as Hlen.
      rewrite Hnil in Hlen.
      rewrite Zlength_nil in Hlen.
      lia.
    }
    rewrite Hlen0 in Hprime.
    unfold prime_len_flag in Hprime.
    simpl in Hprime.
    discriminate.
  }
  rewrite join_words_app_single.
  - replace (start + (i - start)) with i by lia.
    reflexivity.
  - intros word Hin.
    eapply selected_words_nonempty.
    unfold selected_words.
    exact Hin.
  - exact Hseg_nonempty.
Qed.
Lemma Zlength_rev_z : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.
Lemma join_words_cons_bound : forall w ws,
  Zlength (join_words (w :: ws)) <=
  Zlength w + 1 + Zlength (join_words ws).
Proof.
  intros w ws.
  destruct ws as [| a rest].
  - simpl. change (Zlength (@nil Z)) with 0. lia.
  - simpl. rewrite !Zlength_app, Zlength_cons. lia.
Qed.
Lemma words_output_z_aux_len_bound : forall cur rest,
  Zlength
    (join_words
       (List.filter (fun w : list Z => Z.eqb (prime_len_flag (Zlength w)) 1)
          (split_words_z_aux cur rest))) <=
  Zlength cur + Zlength rest.
Proof.
  intros cur rest.
  revert cur.
  induction rest as [| h t IH]; intros cur; simpl.
  - destruct cur as [| z cur].
    + simpl. lia.
    + assert (Zlength (rev (z :: cur)) = Zlength (z :: cur)) as Hrev
        by apply Zlength_rev_z.
      simpl in Hrev.
      simpl.
      rewrite Hrev.
      destruct (Z.eqb (prime_len_flag (Zlength (z :: cur))) 1).
      * simpl. change (Zlength (@nil Z)) with 0.
        rewrite Hrev.
        rewrite Z.add_0_r. apply Z.le_refl.
      * simpl. change (Zlength (@nil Z)) with 0. pose proof Zlength_nonneg (z :: cur). lia.
  - destruct (Z.eqb h 32) eqn:Hspace.
    + destruct cur as [| z cur].
      * specialize (IH []).
        simpl in IH.
        eapply Z.le_trans; [exact IH |].
        replace (Zlength [] + Zlength (h :: t)) with (1 + Zlength t)
          by (rewrite Zlength_cons, Zlength_nil; lia).
        pose proof Zlength_nonneg t. lia.
      * destruct (Z.eqb (prime_len_flag (Zlength (rev (z :: cur)))) 1) eqn:Hsel.
        -- simpl in Hsel. simpl. rewrite Hsel.
           pose proof (join_words_cons_bound (rev (z :: cur))
             (List.filter
                (fun w : list Z => Z.eqb (prime_len_flag (Zlength w)) 1)
                (split_words_z_aux [] t))) as Hbound.
           specialize (IH []).
           simpl in IH.
           rewrite Zlength_rev_z in Hbound.
           eapply Z.le_trans; [exact Hbound |].
           replace (Zlength (h :: t)) with (Z.succ (Zlength t))
             by (rewrite Zlength_cons; reflexivity).
           lia.
        -- simpl in Hsel. simpl. rewrite Hsel.
           specialize (IH []).
           simpl in IH.
           eapply Z.le_trans; [exact IH |].
           replace (Zlength (h :: t)) with (Z.succ (Zlength t))
             by (rewrite Zlength_cons; reflexivity).
           pose proof Zlength_nonneg (z :: cur). lia.
    + specialize (IH (h :: cur)).
      simpl in IH.
      replace (Zlength cur + Zlength (h :: t)) with (Zlength (h :: cur) + Zlength t).
      * exact IH.
      * rewrite !Zlength_cons. lia.
Qed.
Lemma words_in_sentence_prefix_len_bound : forall sentence i,
  0 <= i <= Zlength sentence ->
  Zlength (words_in_sentence_prefix i sentence) <= i.
Proof.
  intros sentence i Hi.
  unfold words_in_sentence_prefix, words_in_sentence_output, selected_words, split_words.
  pose proof (words_output_z_aux_len_bound [] (sublist 0 i sentence)) as Hbound.
  simpl in Hbound.
  rewrite Zlength_sublist0 in Hbound by lia.
  exact Hbound.
Qed.
Lemma words_in_sentence_output_spec : forall sentence,
  problem_143_spec sentence (words_in_sentence_output sentence).
Proof.
  intros sentence.
  unfold problem_143_spec.
  reflexivity.
Qed.
Lemma words_in_sentence_prefix_full : forall sentence i,
  i = Zlength sentence ->
  words_in_sentence_prefix i sentence = words_in_sentence_output sentence.
Proof.
  intros sentence i Hi.
  unfold words_in_sentence_prefix, words_in_sentence_output.
  rewrite sublist_self by exact Hi.
  reflexivity.
Qed.


Lemma proof_of_is_prime_len_entail_wit_1 : is_prime_len_entail_wit_1.
Proof.
  unfold is_prime_len_entail_wit_1.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state.
  split.
  - intro Hbad. lia.
  - intros [d [Hd _]]. lia.
Qed.

Lemma proof_of_is_prime_len_entail_wit_2_1 : is_prime_len_entail_wit_2_1.
Proof.
  unfold is_prime_len_entail_wit_2_1.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state.
  split.
  - intro Hdummy. exists j. split; lia.
  - intro Hdummy. reflexivity.
Qed.

Lemma proof_of_is_prime_len_entail_wit_2_2 : is_prime_len_entail_wit_2_2.
Proof.
  unfold is_prime_len_entail_wit_2_2.
  intros.
  pre_process.
  entailer!.
  unfold prime_loop_state in *.
  destruct H7 as [Hto Hfrom].
  split.
  - intro Hcomp.
    destruct (Hto Hcomp) as [d [Hd Hrem]].
    exists d. split; lia.
  - intros [d [Hd Hrem]].
    assert (d < j \/ d = j) as [Hdlt | ->] by lia.
    + apply Hfrom. exists d. split; lia.
    + contradiction.
Qed.

Lemma proof_of_is_prime_len_return_wit_1 : is_prime_len_return_wit_1.
Proof.
  unfold is_prime_len_return_wit_1.
  intros.
  pre_process.
  assert (composite = 0) by lia.
  subst composite.
  entailer!.
  symmetry.
  eapply (prime_loop_state_flag_1 len_pre j); eauto; lia.
Qed.

Lemma proof_of_is_prime_len_return_wit_2 : is_prime_len_return_wit_2.
Proof.
  unfold is_prime_len_return_wit_2.
  intros.
  pre_process.
  subst composite.
  entailer!.
  symmetry.
  eapply (prime_loop_state_flag_0 len_pre j); eauto; lia.
Qed.

Lemma proof_of_is_prime_len_return_wit_3 : is_prime_len_return_wit_3.
Proof.
  unfold is_prime_len_return_wit_3.
  intros.
  pre_process.
  assert (len_pre = 0 \/ len_pre = 1) as [-> | ->] by lia;
    unfold prime_len_flag, is_prime_bool; simpl; entailer!.
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_1 : p143_words_in_sentence_entail_wit_1.
Proof.
  unfold p143_words_in_sentence_entail_wit_1.
  intros.
  pre_process; subst.
  Exists (@nil Z).
  assert (0 <= 0 <= Zlength l + 2) by lia.
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (Zlength l + 2) H1).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  apply scan_ready_0.
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_3 : p143_words_in_sentence_entail_wit_3.
Proof.
  unfold p143_words_in_sentence_entail_wit_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix i l).
  entailer!.
  - symmetry.
    apply words_in_sentence_prefix_skip_space; lia || assumption.
  - eapply scan_ready_step_space; eauto.
Qed. 

Lemma proof_of_p143_words_in_sentence_entail_wit_4 : p143_words_in_sentence_entail_wit_4.
Proof.
  unfold p143_words_in_sentence_entail_wit_4.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix i l).
  entailer!.
  - apply word_chars_empty.
  - eapply scan_ready_nonspace_start; eauto.
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_5 : p143_words_in_sentence_entail_wit_5.
Proof.
  unfold p143_words_in_sentence_entail_wit_5.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l).
  entailer!.
  eapply word_chars_step; eauto.
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_6_1 : p143_words_in_sentence_entail_wit_6_1.
Proof.
  unfold p143_words_in_sentence_entail_wit_6_1.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l ++ (32 :: nil)).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_0_nonempty; lia).
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  all: try (apply scan_ready_at_end; lia).
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_6_2 : p143_words_in_sentence_entail_wit_6_2.
Proof.
  unfold p143_words_in_sentence_entail_wit_6_2.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l ++ (32 :: nil)).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_0_nonempty; lia).
  all: try (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  all: try (apply scan_ready_at_space; assumption).
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_6_3 : p143_words_in_sentence_entail_wit_6_3.
Proof.
  unfold p143_words_in_sentence_entail_wit_6_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_0_empty; lia).
  all: try (apply scan_ready_at_end; lia).
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_6_4 : p143_words_in_sentence_entail_wit_6_4.
Proof.
  unfold p143_words_in_sentence_entail_wit_6_4.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l).
  entailer!.
  all: try (symmetry; apply word_copy_prefix_0_empty; lia).
  all: try (apply scan_ready_at_space; assumption).
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_7 : p143_words_in_sentence_entail_wit_7.
Proof.
  unfold p143_words_in_sentence_entail_wit_7.
  intros.
  pre_process; subst.
  Exists (word_copy_prefix start (k + 1) l).
  entailer!.
  - rewrite <- word_copy_prefix_step by lia.
    reflexivity.
  - rewrite word_copy_prefix_step by lia.
    rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
Qed.

Lemma proof_of_p143_words_in_sentence_entail_wit_8_2 : p143_words_in_sentence_entail_wit_8_2.
Proof.
  unfold p143_words_in_sentence_entail_wit_8_2.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l).
  entailer!.
  - symmetry.
    eapply words_in_sentence_prefix_nonprime_word; eauto; lia.
  - apply scan_ready_at_end; lia.
Qed. 

Lemma proof_of_p143_words_in_sentence_entail_wit_8_3 : p143_words_in_sentence_entail_wit_8_3.
Proof.
  unfold p143_words_in_sentence_entail_wit_8_3.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_prefix start l).
  entailer!.
  - symmetry.
    eapply words_in_sentence_prefix_nonprime_word; eauto; lia.
  - apply scan_ready_at_space; assumption.
Qed. 

Lemma proof_of_p143_words_in_sentence_entail_wit_8_4 : p143_words_in_sentence_entail_wit_8_4.
Proof.
  unfold p143_words_in_sentence_entail_wit_8_4.
  intros.
  pre_process; subst.
  assert (k = i - start) as Hk by lia.
  Exists (word_copy_prefix start k l).
  entailer!.
  - rewrite Hk.
    symmetry.
    eapply words_in_sentence_prefix_prime_word; eauto; lia.
  - rewrite Hk.
    rewrite <- (words_in_sentence_prefix_prime_word l start i) by (eauto; lia).
    pose proof (words_in_sentence_prefix_len_bound l i ltac:(lia)).
    lia.
Qed. 

Lemma proof_of_p143_words_in_sentence_return_wit_1 : p143_words_in_sentence_return_wit_1.
Proof.
  unfold p143_words_in_sentence_return_wit_1.
  intros.
  pre_process; subst.
  Exists (words_in_sentence_output l) (Zlength (words_in_sentence_output l)).
  assert (i = Zlength l) as Hi by lia.
  assert (words_in_sentence_prefix i l = words_in_sentence_output l) as Hpref.
  { apply words_in_sentence_prefix_full. exact Hi. }
    rewrite Hpref.
    entailer!.
    - rewrite <- Hpref. lia.
    - apply Zlength_nonneg.
Qed.
