(* spec/86 *)
(* def anti_shuffle(s):
"""
Write a function that takes a string and returns an ordered version of it.
Ordered version of string, is a string where all words (separated by space)
are replaced by a new word where all the characters arranged in
ascending order based on ascii value.
Note: You should keep the order of words and blank spaces in the sentence.

For example:
anti_shuffle('Hi') returns 'Hi'
anti_shuffle('hello') returns 'ehllo'
anti_shuffle('Hello World!!!') returns 'Hello !!!Wdlor'
""" *)
(* 引入 Coq 标准库中关于字符串、列表、算术和置换的理论 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Strings.String.

Import ListNotations.
Open Scope string_scope.

Definition is_space_bool (c : ascii) : bool :=
  if ascii_dec c " "%char then true else false.

Fixpoint insert_char_nat (c : ascii) (s : string) : string :=
  match s with
  | EmptyString => String c EmptyString
  | String h t =>
      if Nat.leb (nat_of_ascii c) (nat_of_ascii h) then
        String c s
      else
        String h (insert_char_nat c t)
  end.

Fixpoint sort_chars_nat (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String h t => insert_char_nat h (sort_chars_nat t)
  end.

Fixpoint anti_shuffle_aux (s : string) (acc : string) : string :=
  match s with
  | EmptyString => sort_chars_nat acc
  | String c rest =>
      if is_space_bool c then
        (sort_chars_nat acc) ++ (String c EmptyString) ++ (anti_shuffle_aux rest EmptyString)
      else
        anti_shuffle_aux rest (String c acc)
  end.

Definition anti_shuffle_impl (s : string) : string :=
  anti_shuffle_aux s EmptyString.



Require Import Coq.ZArith.ZArith.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Export string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition problem_86_pre (s : list Z) : Prop :=
  True.

Definition empty_z_list : list Z := [].

Definition is_space (c : Z) : bool :=
  Z.eqb c 32.

Definition ascii_le (a b : Z) : bool :=
  Nat.leb (nat_of_ascii (ascii_of a)) (nat_of_ascii (ascii_of b)).

Fixpoint insert_char (c : Z) (l : list Z) : list Z :=
  match l with
  | [] => [c]
  | h :: t =>
      if ascii_le c h then c :: l else h :: insert_char c t
  end.

Fixpoint sort_chars_forward (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => insert_char h (sort_chars_forward t)
  end.

Definition sort_chars (l : list Z) : list Z :=
  sort_chars_forward (rev l).

Definition anti_step_state (st : list Z * list Z) (c : Z) : list Z * list Z :=
  let '(out_l, cur_l) := st in
  if is_space c then
    (out_l ++ sort_chars cur_l ++ [32], [])
  else
    (out_l, cur_l ++ [c]).

Fixpoint anti_state_nat (n : nat) (l : list Z) : list Z * list Z :=
  match n with
  | O => ([], [])
  | S n' => anti_step_state (anti_state_nat n' l) (Znth (Z.of_nat n') l 0)
  end.

Definition anti_out_prefix (i : Z) (l : list Z) : list Z :=
  fst (anti_state_nat (Z.to_nat i) l).

Definition anti_cur_prefix (i : Z) (l : list Z) : list Z :=
  snd (anti_state_nat (Z.to_nat i) l).

Definition anti_shuffle_output (l : list Z) : list Z :=
  anti_out_prefix (Zlength l) l ++ sort_chars (anti_cur_prefix (Zlength l) l).

Definition problem_86_spec (s output : list Z) : Prop :=
  string_of_list output = anti_shuffle_impl (string_of_list s).

Fixpoint anti_process (l cur : list Z) : list Z :=
  match l with
  | [] => sort_chars cur
  | c :: rest =>
      if is_space c then
        sort_chars cur ++ [32] ++ anti_process rest []
      else
        anti_process rest (cur ++ [c])
  end.

Lemma nat_of_ascii_ascii_of : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  rewrite nat_ascii_embedding by lia.
  reflexivity.
Qed.

Lemma Zlength_insert_char : forall c l,
  Zlength (insert_char c l) = Zlength l + 1.
Proof.
  intros c l.
  induction l as [| h t IH]; simpl.
  - rewrite Zlength_cons, Zlength_nil. lia.
  - unfold ascii_le.
    destruct (Nat.leb _ _); simpl.
    + repeat rewrite Zlength_cons. lia.
    + repeat rewrite Zlength_cons. lia.
Qed.

Lemma Zlength_sort_chars_forward : forall l,
  Zlength (sort_chars_forward l) = Zlength l.
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - rewrite Zlength_insert_char, IH.
    rewrite Zlength_cons. lia.
Qed.

Lemma Zlength_rev_86 : forall (l : list Z),
  Zlength (rev l) = Zlength l.
Proof.
  intros l.
  rewrite !Zlength_correct, List.rev_length.
  reflexivity.
Qed.

Lemma Zlength_sort_chars : forall l,
  Zlength (sort_chars l) = Zlength l.
Proof.
  intros l.
  unfold sort_chars.
  rewrite Zlength_sort_chars_forward.
  rewrite Zlength_rev_86.
  reflexivity.
Qed.

Lemma anti_state_nat_out_cur_len : forall n l,
  (Z.of_nat n <= Zlength l)%Z ->
  Zlength (fst (anti_state_nat n l)) + Zlength (snd (anti_state_nat n l)) =
  Z.of_nat n.
Proof.
  induction n as [| n IH]; intros l Hn; simpl.
  - reflexivity.
  - specialize (IH l ltac:(lia)).
    destruct (anti_state_nat n l) as [out_l cur_l].
    simpl in *.
    unfold anti_step_state.
    destruct (is_space (Znth (Z.of_nat n) l 0)) eqn:Hspace; simpl.
    + rewrite !Zlength_app, Zlength_sort_chars.
      rewrite !Zlength_cons, !Zlength_nil.
      lia.
    + rewrite Zlength_app, Zlength_cons, Zlength_nil.
      lia.
Qed.

Lemma anti_prefix_lengths : forall i l,
  0 <= i <= Zlength l ->
  Zlength (anti_out_prefix i l) + Zlength (anti_cur_prefix i l) = i.
Proof.
  intros i l Hi.
  unfold anti_out_prefix, anti_cur_prefix.
  pose proof (anti_state_nat_out_cur_len (Z.to_nat i) l ltac:(lia)).
  lia.
Qed.

Lemma Znth_app_l_0_86 : forall l i,
  0 <= i < Zlength l ->
  Znth i (l ++ [0]) 0 = Znth i l 0.
Proof.
  intros l i Hi.
  rewrite app_Znth1 by lia.
  reflexivity.
Qed.

Lemma anti_state_nat_step_86 : forall i l,
  0 <= i ->
  anti_state_nat (Z.to_nat (i + 1)) l =
  anti_step_state (anti_state_nat (Z.to_nat i) l) (Znth i l 0).
Proof.
  intros i l Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  simpl.
  replace (Z.of_nat (Z.to_nat i)) with i by lia.
  reflexivity.
Qed.

Lemma anti_prefix_step_nonspace_86 : forall i l,
  0 <= i ->
  is_space (Znth i l 0) = false ->
  anti_out_prefix (i + 1) l = anti_out_prefix i l /\
  anti_cur_prefix (i + 1) l = anti_cur_prefix i l ++ [Znth i l 0].
Proof.
  intros i l Hi Hspace.
  unfold anti_out_prefix, anti_cur_prefix.
  rewrite anti_state_nat_step_86 by lia.
  destruct (anti_state_nat (Z.to_nat i) l) as [out_l cur_l].
  unfold anti_step_state.
  rewrite Hspace.
  split; reflexivity.
Qed.

Lemma anti_prefix_step_space_86 : forall i l,
  0 <= i ->
  is_space (Znth i l 0) = true ->
  anti_out_prefix (i + 1) l =
    anti_out_prefix i l ++ sort_chars (anti_cur_prefix i l) ++ [32] /\
  anti_cur_prefix (i + 1) l = [].
Proof.
  intros i l Hi Hspace.
  unfold anti_out_prefix, anti_cur_prefix.
  rewrite anti_state_nat_step_86 by lia.
  destruct (anti_state_nat (Z.to_nat i) l) as [out_l cur_l].
  unfold anti_step_state.
  rewrite Hspace.
  split; reflexivity.
Qed.

Lemma is_space_eq_true_86 : forall c,
  c = 32 ->
  is_space c = true.
Proof.
  intros c ->.
  unfold is_space.
  rewrite Z.eqb_refl.
  reflexivity.
Qed.

Lemma is_space_eq_false_86 : forall c,
  c <> 32 ->
  is_space c = false.
Proof.
  intros c Hneq.
  unfold is_space.
  apply Z.eqb_neq.
  exact Hneq.
Qed.

Lemma anti_shuffle_output_length_86 : forall l,
  Zlength (anti_shuffle_output l) = Zlength l.
Proof.
  intros l.
  unfold anti_shuffle_output.
  rewrite Zlength_app, Zlength_sort_chars.
  pose proof (Zlength_nonneg l) as Hlen_nonneg.
  pose proof (anti_prefix_lengths (Zlength l) l ltac:(lia)).
  lia.
Qed.

Lemma string_of_list_app_86 : forall l1 l2,
  string_of_list (l1 ++ l2) =
  String.append (string_of_list l1) (string_of_list l2).
Proof.
  induction l1 as [| c rest IH]; intros l2; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma ascii_of_space_86 : ascii_of 32 = " "%char.
Proof.
  reflexivity.
Qed.

Lemma ascii_of_eq_space_to_code_86 : forall x,
  0 <= x < 256 ->
  ascii_of x = " "%char ->
  x = 32.
Proof.
  intros x Hrange Hspace.
  apply (f_equal nat_of_ascii) in Hspace.
  rewrite nat_of_ascii_ascii_of in Hspace by exact Hrange.
  change (nat_of_ascii " "%char) with 32%nat in Hspace.
  lia.
Qed.

Lemma is_space_bool_ascii_of_86 : forall c,
  0 <= c < 256 ->
  is_space_bool (ascii_of c) = is_space c.
Proof.
  intros c Hrange.
  unfold is_space_bool, is_space.
  destruct (ascii_dec (ascii_of c) " "%char) as [Hspace | Hspace].
  - apply ascii_of_eq_space_to_code_86 in Hspace; try assumption.
    subst c.
    rewrite Z.eqb_refl.
    reflexivity.
  - destruct (Z.eqb_spec c 32) as [Heq | Hneq].
    + subst c.
      exfalso.
      apply Hspace.
      apply ascii_of_space_86.
    + reflexivity.
Qed.

Lemma ascii_range_cons_inv_86 : forall c rest,
  ascii_range (c :: rest) ->
  0 <= c < 256 /\ ascii_range rest.
Proof.
  intros c rest Hrange.
  split.
  - assert (Hidx : 0 <= 0 < Zlength (c :: rest)).
    { rewrite Zlength_cons.
      pose proof (Zlength_nonneg rest).
      lia. }
    specialize (Hrange 0 Hidx).
    unfold Znth in Hrange.
    simpl in Hrange.
    exact Hrange.
  - unfold ascii_range in *.
    intros i Hi.
    assert (Hidx : 0 <= i + 1 < Zlength (c :: rest)).
    { rewrite Zlength_cons in *.
      lia. }
    specialize (Hrange (i + 1) Hidx).
    unfold Znth in *.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) in Hrange by lia.
    simpl in Hrange.
    exact Hrange.
Qed.

Lemma string_of_list_insert_char_86 : forall c l,
  string_of_list (insert_char c l) =
  insert_char_nat (ascii_of c) (string_of_list l).
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - unfold ascii_le.
    destruct (Nat.leb _ _); simpl.
    + reflexivity.
    + rewrite IH.
      reflexivity.
Qed.

Lemma string_of_list_sort_chars_forward_86 : forall l,
  string_of_list (sort_chars_forward l) =
  sort_chars_nat (string_of_list l).
Proof.
  induction l as [| h t IH]; simpl.
  - reflexivity.
  - rewrite string_of_list_insert_char_86.
    rewrite IH.
    reflexivity.
Qed.

Lemma string_of_list_sort_chars_86 : forall l,
  string_of_list (sort_chars l) =
  sort_chars_nat (string_of_list (rev l)).
Proof.
  intros l.
  unfold sort_chars.
  apply string_of_list_sort_chars_forward_86.
Qed.

Lemma string_of_list_rev_snoc_86 : forall cur c,
  string_of_list (rev (cur ++ [c])) =
  String (ascii_of c) (string_of_list (rev cur)).
Proof.
  intros cur c.
  rewrite rev_app_distr.
  simpl.
  reflexivity.
Qed.

Lemma Znth_of_nat_nth_86 : forall {A : Type} n (l : list A) d,
  Znth (Z.of_nat n) l d = nth n l d.
Proof.
  intros A n l d.
  unfold Znth.
  rewrite Nat2Z.id.
  reflexivity.
Qed.

Lemma skipn_n_cons_86 : forall {A : Type} n (l : list A) d,
  (n < Datatypes.length l)%nat ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  intros A n.
  induction n as [| n IH]; intros l d Hlen.
  - destruct l as [| c rest]; simpl in *; try lia.
    reflexivity.
  - destruct l as [| c rest]; simpl in *; try lia.
    apply IH.
    lia.
Qed.

Lemma app_space_tail_86 : forall a b rest,
  (a ++ b ++ [32]) ++ rest = a ++ b ++ 32 :: rest.
Proof.
  intros a b rest.
  repeat rewrite <- List.app_assoc.
  reflexivity.
Qed.

Lemma anti_state_nat_process_86 : forall n l,
  (n <= Datatypes.length l)%nat ->
  fst (anti_state_nat n l) ++
    anti_process (skipn n l) (snd (anti_state_nat n l)) =
  anti_process l [].
Proof.
  induction n as [| n IH]; intros l Hlen.
  - simpl.
    reflexivity.
  - assert (Hn_le : (n <= Datatypes.length l)%nat) by lia.
    assert (Hn_lt : (n < Datatypes.length l)%nat) by lia.
    pose proof (IH l Hn_le) as Hprev.
    rewrite <- Hprev.
    simpl anti_state_nat.
    rewrite (skipn_n_cons_86 n l 0 Hn_lt).
    rewrite Znth_of_nat_nth_86.
    destruct (anti_state_nat n l) as [out_l cur_l].
    simpl.
    unfold anti_step_state.
    destruct (is_space (nth n l 0)) eqn:Hspace; simpl.
    + rewrite app_space_tail_86.
      reflexivity.
    + reflexivity.
Qed.

Lemma anti_shuffle_output_eq_process_86 : forall l,
  anti_shuffle_output l = anti_process l [].
Proof.
  intros l.
  unfold anti_shuffle_output, anti_out_prefix, anti_cur_prefix.
  pose proof (anti_state_nat_process_86 (Datatypes.length l) l ltac:(lia)) as Hprocess.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite skipn_all in Hprocess.
  simpl in Hprocess.
  exact Hprocess.
Qed.

Lemma anti_process_correct_86 : forall l cur,
  ascii_range l ->
  string_of_list (anti_process l cur) =
  anti_shuffle_aux (string_of_list l) (string_of_list (rev cur)).
Proof.
  induction l as [| c rest IH]; intros cur Hrange.
  - simpl.
    apply string_of_list_sort_chars_86.
  - destruct (ascii_range_cons_inv_86 c rest Hrange) as [Hc Hrest].
    simpl.
    rewrite is_space_bool_ascii_of_86 by exact Hc.
    unfold is_space.
    destruct (Z.eqb_spec c 32) as [Hspace | Hnonspace].
    + subst c.
      simpl.
      rewrite !string_of_list_app_86.
      simpl.
      rewrite string_of_list_sort_chars_86.
      rewrite IH by exact Hrest.
      rewrite ascii_of_space_86.
      reflexivity.
    + rewrite IH by exact Hrest.
      rewrite string_of_list_rev_snoc_86.
      reflexivity.
Qed.

Lemma problem_86_spec_anti_shuffle_output_86 : forall l,
  ascii_range l ->
  problem_86_spec l (anti_shuffle_output l).
Proof.
  intros l Hrange.
  unfold problem_86_spec, problem_86_spec, anti_shuffle_impl.
  rewrite anti_shuffle_output_eq_process_86.
  apply anti_process_correct_86.
  exact Hrange.
Qed.

Lemma Forall_Znth_nonzero_86 : forall l p,
  Forall (fun x => x <> 0) l ->
  0 <= p < Zlength l ->
  Znth p l 0 <> 0.
Proof.
  intros l p Hforall Hp.
  unfold Znth.
  apply Forall_forall with (x := nth (Z.to_nat p) l 0) in Hforall.
  - exact Hforall.
  - apply nth_In.
    rewrite Zlength_correct in Hp.
    lia.
Qed.

Lemma Znth_nonzero_Forall_86 : forall l,
  (forall k, 0 <= k < Zlength l -> Znth k l 0 <> 0) ->
  Forall (fun x => x <> 0) l.
Proof.
  induction l as [| h t IH]; intros Hnonzero.
  - constructor.
  - constructor.
    + specialize (Hnonzero 0).
      assert (0 <= 0 < Zlength (h :: t)).
      { rewrite Zlength_cons.
        pose proof (Zlength_nonneg t).
        lia. }
      specialize (Hnonzero H).
      unfold Znth in Hnonzero.
      simpl in Hnonzero.
      exact Hnonzero.
    + apply IH.
      intros k Hk.
      specialize (Hnonzero (k + 1)).
      assert (0 <= k + 1 < Zlength (h :: t)).
      { rewrite Zlength_cons.
        lia. }
      specialize (Hnonzero H).
      unfold Znth in Hnonzero.
      replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) in Hnonzero by lia.
      simpl in Hnonzero.
      exact Hnonzero.
Qed.

Lemma insert_char_nonzero_forall_86 : forall c l,
  c <> 0 ->
  Forall (fun x => x <> 0) l ->
  Forall (fun x => x <> 0) (insert_char c l).
Proof.
  intros c l Hc Hl.
  induction Hl as [| h t Hh Ht IH]; simpl.
  - constructor; [exact Hc | constructor].
  - unfold ascii_le.
    destruct (Nat.leb _ _); simpl.
    + constructor; [exact Hc | constructor; assumption].
    + constructor; [exact Hh | exact IH].
Qed.

Lemma sort_chars_forward_nonzero_forall_86 : forall l,
  Forall (fun x => x <> 0) l ->
  Forall (fun x => x <> 0) (sort_chars_forward l).
Proof.
  intros l Hl.
  induction Hl as [| h t Hh Ht IH]; simpl.
  - constructor.
  - apply insert_char_nonzero_forall_86; assumption.
Qed.

Lemma sort_chars_nonzero_forall_86 : forall l,
  Forall (fun x => x <> 0) l ->
  Forall (fun x => x <> 0) (sort_chars l).
Proof.
  intros l Hl.
  unfold sort_chars.
  apply sort_chars_forward_nonzero_forall_86.
  apply Forall_rev.
  exact Hl.
Qed.

Lemma anti_process_nonzero_forall_86 : forall l cur,
  Forall (fun x => x <> 0) l ->
  Forall (fun x => x <> 0) cur ->
  Forall (fun x => x <> 0) (anti_process l cur).
Proof.
  induction l as [| c rest IH]; intros cur Hl Hcur; simpl.
  - apply sort_chars_nonzero_forall_86.
    exact Hcur.
  - inversion Hl as [| ? ? Hc Hrest]; subst.
    destruct (is_space c) eqn:Hspace.
    + apply Forall_app.
      split.
      * apply sort_chars_nonzero_forall_86.
        exact Hcur.
      * constructor; [lia | apply IH; [exact Hrest | constructor]].
    + apply IH.
      * exact Hrest.
      * apply Forall_app.
        split; [exact Hcur | constructor; [exact Hc | constructor]].
Qed.

Lemma anti_shuffle_output_nonzero_forall_86 : forall l,
  Forall (fun x => x <> 0) l ->
  Forall (fun x => x <> 0) (anti_shuffle_output l).
Proof.
  intros l Hl.
  rewrite anti_shuffle_output_eq_process_86.
  apply anti_process_nonzero_forall_86.
  - exact Hl.
  - constructor.
Qed.

Lemma anti_shuffle_output_Znth_nonzero_86 : forall l k,
  (forall j, 0 <= j < Zlength l -> Znth j l 0 <> 0) ->
  0 <= k < Zlength (anti_shuffle_output l) ->
  Znth k (anti_shuffle_output l) 0 <> 0.
Proof.
  intros l k Hinput Hk.
  eapply Forall_Znth_nonzero_86.
  - apply anti_shuffle_output_nonzero_forall_86.
    apply Znth_nonzero_Forall_86.
    exact Hinput.
  - exact Hk.
Qed.
