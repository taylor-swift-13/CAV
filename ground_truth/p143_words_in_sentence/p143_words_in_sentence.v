(* spec/143 *)
(* def words_in_sentence(sentence):
"""
You are given a string representing a sentence,
the sentence contains some words separated by a space,
and you have to return a string that contains the words from the original sentence,
whose lengths are prime numbers,
the order of the words in the new string should be the same as the original one.

Example 1:
Input: sentence = "This is a test"
Output: "is"

Example 2:
Input: sentence = "lets go for swimming"
Output: "go for"

Constraints:
* 1 <= len(sentence) <= 100
* sentence contains only letters
""" *)

Require Import Coq.Lists.List Coq.Strings.Ascii Coq.Strings.String Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint has_divisor_from (n d : nat) : bool :=
  match d with
  | 0 => false
  | 1 => false
  | S d' =>
    if (n mod d =? 0)%nat then
      true
    else
      has_divisor_from n d'
  end.

Definition is_prime_bool (n : nat) : bool :=
  match n with
  | 0 | 1 => false
  | _ => negb (has_divisor_from n (n - 1))
  end.

Definition split_words_nat (s : list ascii) : list (list ascii) :=
  let space := " "%char in
  let fix aux (cur : list ascii) (rest : list ascii) : list (list ascii) :=
    match rest with
    | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
    | h :: t =>
      if Ascii.eqb h space then
        match cur with
        | [] => aux [] t
        | _ => (rev cur) :: aux [] t
        end
      else
        aux (h :: cur) t
    end
  in aux [] s.

Fixpoint join_words_nat (ws : list (list ascii)) : list ascii :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest =>
    w ++ (" "%char :: nil) ++ join_words_nat rest
  end.

Definition words_in_sentence_impl (sentence : string) : string :=
  let words := split_words_nat (list_ascii_of_string sentence) in
  let sel := List.filter (fun w => is_prime_bool (List.length w)) words in
  string_of_list_ascii (join_words_nat sel).

(* 约束：1 <= 长度 <= 100；内容为英文字母或空格 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_143_pre (sentence : list Z) : Prop :=
  1 <= Zlength sentence <= 100 /\
  forall i, 0 <= i < Zlength sentence ->
    Znth i sentence 0 = 32 \/
    65 <= Znth i sentence 0 <= 90 \/
    97 <= Znth i sentence 0 <= 122.

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition z_of_ascii (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Fixpoint list_z_of_string (s : string) : list Z :=
  match s with
  | EmptyString => []
  | String c rest => z_of_ascii c :: list_z_of_string rest
  end.

Definition prime_len_flag (n : Z) : Z :=
  if is_prime_bool (Z.to_nat n) then 1 else 0.

Fixpoint split_words_z_aux (cur rest : list Z) : list (list Z) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Z.eqb h 32 then
        match cur with
        | [] => split_words_z_aux [] t
        | _ => rev cur :: split_words_z_aux [] t
        end
      else split_words_z_aux (h :: cur) t
  end.

Definition split_words (sentence : list Z) : list (list Z) :=
  split_words_z_aux [] sentence.

Fixpoint split_words_ascii_aux (cur rest : list ascii) : list (list ascii) :=
  match rest with
  | [] =>
      match cur with
      | [] => []
      | _ => [rev cur]
      end
  | h :: t =>
      if Ascii.eqb h " "%char then
        match cur with
        | [] => split_words_ascii_aux [] t
        | _ => rev cur :: split_words_ascii_aux [] t
        end
      else split_words_ascii_aux (h :: cur) t
  end.

Definition split_words_ascii (sentence : list ascii) : list (list ascii) :=
  split_words_ascii_aux [] sentence.

Definition split_words_spec_aux (cur rest : list ascii) : list (list ascii) :=
  (fix aux (cur rest : list ascii) {struct rest} : list (list ascii) :=
     match rest with
     | [] =>
         match cur with
         | [] => []
         | _ => [rev cur]
         end
     | h :: t =>
         if Ascii.eqb h " "%char then
           match cur with
           | [] => aux [] t
           | _ => rev cur :: aux [] t
           end
         else aux (h :: cur) t
     end) cur rest.

Definition words_output_ascii (s : list ascii) : list ascii :=
  join_words_nat
    (List.filter (fun w => is_prime_bool (List.length w)) (split_words_nat s)).

Fixpoint join_words (ws : list (list Z)) : list Z :=
  match ws with
  | [] => []
  | w :: nil => w
  | w :: rest => w ++ [32] ++ join_words rest
  end.

Definition selected_words (sentence : list Z) : list (list Z) :=
  List.filter (fun w => Z.eqb (prime_len_flag (Zlength w)) 1)
    (split_words sentence).

Definition words_in_sentence_output (sentence : list Z) : list Z :=
  join_words (selected_words sentence).

Definition problem_143_spec (sentence output : list Z) : Prop :=
  output = words_in_sentence_output sentence.

Definition words_in_sentence_prefix (i : Z) (sentence : list Z) : list Z :=
  words_in_sentence_output (sublist 0 i sentence).

Definition prime_loop_state (n j composite : Z) : Prop :=
  composite = 1 <->
    exists d, 2 <= d < j /\ Z.rem n d = 0.

Definition append_selected_word
    (out prefix : list Z) (start len : Z) : list Z :=
  if Z.eqb (prime_len_flag len) 1 then
    out ++ (if Z.eqb (Zlength out) 0 then [] else [32]) ++
    sublist start (start + len) prefix
  else out.

Definition word_chars (sentence : list Z) (start i : Z) : Prop :=
  forall p, start <= p < i -> Znth p (sentence ++ [0]) 0 <> 32.

Definition word_start (sentence : list Z) (start : Z) : Prop :=
  start = 0 \/ Znth (start - 1) (sentence ++ [0]) 0 = 32.

Definition scan_ready (sentence : list Z) (len i : Z) : Prop :=
  i = 0 \/
  i = len \/
  Znth i (sentence ++ [0]) 0 = 32 \/
  Znth (i - 1) (sentence ++ [0]) 0 = 32.

Definition word_copy_prefix (start k : Z) (sentence : list Z) : list Z :=
  words_in_sentence_prefix start sentence ++
  (if Z.eqb (Zlength (words_in_sentence_prefix start sentence)) 0
   then [] else [32]) ++
  sublist start (start + k) sentence.

Definition nonspace_z_list (w : list Z) : Prop :=
  forall x, In x w -> x <> 32.

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
