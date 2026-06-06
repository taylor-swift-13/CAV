(* spec/91 *)
(* def is_bored(S):
"""
You'll be given a string of words, and your task is to count the number
of boredoms. A boredom is a sentence that starts with the word "I".
Sentences are delimited by '.', '?' or '!'.

For example:
>>> is_bored("Hello world")
0
>>> is_bored("The sky is blue. The sun is shining. I love this weather")
1
""" *)

Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_sentence_delimiter (c : ascii) : bool :=
  match c with
  | "."%char | "?"%char | "!"%char => true
  | _ => false
  end.

Fixpoint is_bored_aux (S : string) (isstart isi : bool) : nat :=
  match S with
  | "" => 0
  | String c rest =>
    let add := if andb (Ascii.eqb c " "%char) isi then 1 else 0 in
    let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
    let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
    let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
    add + is_bored_aux rest isstart' isi'
  end.

Definition is_bored_impl (S : string) : nat :=
  is_bored_aux S true false.

(* 输入字符串可为任意内容，无额外约束 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition zbool (b : bool) : Z := if b then 1 else 0.

Definition z_is_space (c : Z) : bool := Z.eqb c 32.
Definition z_is_i (c : Z) : bool := Z.eqb c 73.
Definition z_is_delim (c : Z) : bool :=
  orb (orb (Z.eqb c 46) (Z.eqb c 63)) (Z.eqb c 33).

Definition bored_add (c isi : Z) : Z :=
  zbool (andb (z_is_space c) (Z.eqb isi 1)).

Definition bored_next_isi (c isstart : Z) : Z :=
  zbool (andb (z_is_i c) (Z.eqb isstart 1)).

Definition bored_next_isstart (c isstart : Z) : Z :=
  if z_is_delim c then 1
  else if z_is_space c then isstart
  else 0.

Fixpoint bored_state_after_nat (k : nat) (l : list Z) : Z * Z * Z :=
  match k with
  | O => (0, 1, 0)
  | S k' =>
      let '(sum, isstart, isi) := bored_state_after_nat k' l in
      let c := Znth (Z.of_nat k') l 0 in
      (sum + bored_add c isi,
       bored_next_isstart c isstart,
       bored_next_isi c isstart)
  end.

Definition bored_sum_prefix (i : Z) (l : list Z) : Z :=
  let '(sum, _, _) := bored_state_after_nat (Z.to_nat i) l in sum.

Definition bored_isstart_prefix (i : Z) (l : list Z) : Z :=
  let '(_, isstart, _) := bored_state_after_nat (Z.to_nat i) l in isstart.

Definition bored_isi_prefix (i : Z) (l : list Z) : Z :=
  let '(_, _, isi) := bored_state_after_nat (Z.to_nat i) l in isi.

Definition problem_91_pre (s : list Z) : Prop :=
  True.

Definition bored_step_z_state (st : Z * Z * Z) (c : Z) : Z * Z * Z :=
  let '(sum, isstart, isi) := st in
  (sum + bored_add c isi,
   bored_next_isstart c isstart,
   bored_next_isi c isstart).

Fixpoint bored_state_list (l : list Z) (st : Z * Z * Z) : Z * Z * Z :=
  match l with
  | [] => st
  | c :: rest => bored_state_list rest (bored_step_z_state st c)
  end.

Definition problem_91_spec (s : list Z) (output : Z) : Prop :=
  let '(sum, _, _) := bored_state_list s (0, 1, 0) in
  output = sum.

Definition bored_step_ascii_state
    (st : nat * bool * bool) (c : ascii) : nat * bool * bool :=
  let '(sum, isstart, isi) := st in
  let add := if andb (Ascii.eqb c " "%char) isi then 1%nat else 0%nat in
  let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
  let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
  let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
  ((sum + add)%nat, isstart', isi').

Fixpoint bored_state_list_ascii
    (l : list ascii) (st : nat * bool * bool) : nat * bool * bool :=
  match l with
  | [] => st
  | c :: rest => bored_state_list_ascii rest (bored_step_ascii_state st c)
  end.

Fixpoint is_bored_ascii_list (l : list ascii) (isstart isi : bool) : nat :=
  match l with
  | [] => 0%nat
  | c :: rest =>
      let add := if andb (Ascii.eqb c " "%char) isi then 1%nat else 0%nat in
      let isi' := if andb (Ascii.eqb c "I"%char) isstart then true else false in
      let isstart_after_char := if Ascii.eqb c " "%char then isstart else false in
      let isstart' := if is_sentence_delimiter c then true else isstart_after_char in
      (add + is_bored_ascii_list rest isstart' isi')%nat
  end.

Definition state_rel (zst : Z * Z * Z) (ast : nat * bool * bool) : Prop :=
  let '(zsum, zisstart, zisi) := zst in
  let '(asum, aisstart, aisi) := ast in
  zsum = Z.of_nat asum /\ zisstart = zbool aisstart /\ zisi = zbool aisi.
