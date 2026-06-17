(* spec/161 *)
(* def solve(s):
"""You are given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
solve("1234") = "4321"
solve("ab") = "AB"
solve("#a@C") = "#A@c"
""" *)
(* 引入所需的库 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith. (* 需要引入这个库来进行自然数运算 *)
Require Import Coq.Strings.String.
Import ListNotations.

(*
  辅助定义
*)

(* 判断一个 ascii 字符是否为小写字母 *)
Definition is_lower_alpha (a : ascii) : bool :=
  (("a"%char <=? a)%char && (a <=? "z"%char)%char).

(* 判断一个 ascii 字符是否为大写字母 *)
Definition is_upper_alpha (a : ascii) : bool :=
  (("A"%char <=? a)%char && (a <=? "Z"%char)%char).

(* 判断一个 ascii 字符是否为字母 *)
Definition is_letter_dec (a : ascii) : bool :=
  is_lower_alpha a || is_upper_alpha a.

(* 自定义的大小写转换函数 *)

(* 将小写字母转为大写。如果不是小写字母，则保持不变。
   原理：nat_of_ascii a - 32 *)
Definition my_uppercase (a : ascii) : ascii :=
  if is_lower_alpha a
  then ascii_of_nat (nat_of_ascii a - 32)
  else a.

(* 将大写字母转为小写。如果不是大写字母，则保持不变。
   原理：nat_of_ascii a + 32 *)
Definition my_lowercase (a : ascii) : ascii :=
  if is_upper_alpha a
  then ascii_of_nat (nat_of_ascii a + 32)
  else a.

(* 定义一个函数 change_case 来转换字母的大小写。
   现在它使用我们自定义的转换函数。 *)
Definition change_case (a : ascii) : ascii :=
  if is_lower_alpha a then
    my_uppercase a
  else if is_upper_alpha a then
    my_lowercase a
  else
    a.

(* 定义一个递归函数 contains_letter_dec 来判断一个列表 (字符串) 是否包含任何字母。*)
Fixpoint contains_letter_dec (s : list ascii) : bool :=
  match s with
  | [] => false
  | h :: t => is_letter_dec h || contains_letter_dec t
  end.

Definition solve_impl (s : string) : string :=
  let l := list_ascii_of_string s in
  if contains_letter_dec l
  then string_of_list_ascii (map change_case l)
  else string_of_list_ascii (rev l).

(* 任意字符串输入 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.BinNat.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition is_lower_zb (c : Z) : bool :=
  (Z.leb 97 c) && (Z.leb c 122).

Definition is_upper_zb (c : Z) : bool :=
  (Z.leb 65 c) && (Z.leb c 90).

Definition is_letter_zb (c : Z) : bool :=
  is_lower_zb c || is_upper_zb c.

Definition flip_char (c : Z) : Z :=
  if is_lower_zb c then c - 32
  else if is_upper_zb c then c + 32
  else c.

Fixpoint contains_letter_list (l : list Z) : bool :=
  match l with
  | [] => false
  | c :: rest => is_letter_zb c || contains_letter_list rest
  end.

Definition contains_letter_prefix (i : Z) (l : list Z) : Z :=
  if contains_letter_list (firstn (Z.to_nat i) l) then 1 else 0.

Definition contains_letter (l : list Z) : Z :=
  if contains_letter_list l then 1 else 0.

Definition problem_161_pre (s : list Z) : Prop :=
  True.

Definition problem_161_spec (input output : list Z) : Prop :=
  string_of_list output = solve_impl (string_of_list input).

(* Helper lemmas migrated from the old proof, with names aligned to the input spec. *)
Lemma contains_letter_list_app : forall a b,
  contains_letter_list (a ++ b) =
  contains_letter_list a || contains_letter_list b.
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
