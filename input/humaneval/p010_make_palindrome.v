Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.

Definition palindrome (s : string) : Prop :=
  s = string_of_list_ascii (List.rev (list_ascii_of_string s)).

Definition problem_10_pre (input : list Z) : Prop :=
  True.

Definition problem_10_spec (input output : list Z) : Prop :=
  prefix (string_of_list input) (string_of_list output) = true /\
  palindrome (string_of_list output) /\
  forall p : string,
    prefix (string_of_list input) p = true /\
    palindrome p ->
    Zlength output <= Zlength (list_ascii_of_string p).

Definition pal_suffix (start : Z) (input : list Z) : Prop :=
  0 <= start <= Zlength input /\
  forall k,
    0 <= k < Zlength input - start ->
    k < Zlength input - start - 1 - k ->
    Znth (start + k) input 0 = Znth (Zlength input - 1 - k) input 0.

Definition first_pal_suffix (best : Z) (input : list Z) : Prop :=
  0 <= best <= Zlength input /\
  pal_suffix best input /\
  forall t, 0 <= t < best -> ~ pal_suffix t input.

Definition make_pal_output (best : Z) (input : list Z) : list Z :=
  input ++ rev (firstn (Z.to_nat best) input).
