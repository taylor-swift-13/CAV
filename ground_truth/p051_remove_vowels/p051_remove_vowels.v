(* spec/51 *)
(* def remove_vowels(text):
"""
remove_vowels is a function that takes string and returns string without vowels.
>>> remove_vowels('')
''
>>> remove_vowels("abcdef\nghijklm")
'bcdf\nghjklm'
>>> remove_vowels('abcdef')
'bcdf'
>>> remove_vowels('aaaaa')
''
>>> remove_vowels('aaBAA')
'B'
>>> remove_vowels('zbcd')
'zbcd'
""" *)
(* 导入 Coq 标准库中的 ASCII 字符和列表模块 *)
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(*
 * 描述: 判断一个 ASCII 字符是否是元音字母（包括大小写）。
 * @param c: ascii - 输入的字符。
 * @return: bool - 如果是元音则返回 true，否则返回 false。
 * )
*)
Definition is_vowel_nat (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

Fixpoint filter_string (f : ascii -> bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if f c then String c (filter_string f s') else filter_string f s'
  end.

(*
 * 描述: 这是 remove_vowels 函数的程序规约 (Specification)，完全基于属性定义。
 * 它将输出列表 (output) 定义为输入列表 (input) 中所有非元音字母的集合。
 *
 * @param input: string - 输入的原始字符列表。
 * @param output: string - 函数的输出字符列表。
 * @return: Prop - 一个表示输入和输出之间关系的命题。
 *)
(* Pre: no special constraints for `remove_vowels` *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.

Definition problem_51_pre (s : list Z) : Prop :=
  True.

Definition char_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition is_vowel (c : Z) : bool :=
  orb (Z.eqb c 65)
  (orb (Z.eqb c 69)
  (orb (Z.eqb c 73)
  (orb (Z.eqb c 79)
  (orb (Z.eqb c 85)
  (orb (Z.eqb c 97)
  (orb (Z.eqb c 101)
  (orb (Z.eqb c 105)
  (orb (Z.eqb c 111) (Z.eqb c 117))))))))).

Fixpoint remove_vowels_list (s : list Z) : list Z :=
  match s with
  | [] => []
  | c :: rest =>
      if is_vowel c
      then remove_vowels_list rest
      else c :: remove_vowels_list rest
  end.

Definition remove_vowels_prefix (i : Z) (s : list Z) : list Z :=
  remove_vowels_list (firstn (Z.to_nat i) s).

Definition problem_51_spec (input output : list Z) : Prop :=
  string_of_list output = filter_string (fun c => negb (is_vowel_nat c)) (string_of_list input).

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
