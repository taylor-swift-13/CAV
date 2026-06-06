(* spec/27 *)
(* """ For a given string, flip lowercase characters to uppercase and uppercase to lowercase.
>>> flip_case('Hello')
'hELLO'
""" *)

(* Spec(input : string, output : string) :=

​	length(input) = length(output) ∧
​	∀i ∈ [0, length(input)),  IsLow(input[i]) → output[i] = Upper(input[i]) ∧ IsUp(input[i]) → output[i] = Lower(input[i])*)

Require Import String Ascii Arith Bool.

Definition IsLow (c : ascii) : Prop :=
  (nat_of_ascii "a" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "z")%nat.

Definition IsUp (c : ascii) : Prop :=
  (nat_of_ascii "A" <= nat_of_ascii c)%nat /\
  (nat_of_ascii c <= nat_of_ascii "Z")%nat.

Definition Upper (c : ascii) : ascii :=
  if (nat_of_ascii "a" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "z")%nat
  then ascii_of_nat (nat_of_ascii c - 32)
  else c.

Definition Lower (c : ascii) : ascii :=
  if (nat_of_ascii "A" <=? nat_of_ascii c)%nat &&
     (nat_of_ascii c <=? nat_of_ascii "Z")%nat
  then ascii_of_nat (nat_of_ascii c + 32)
  else c.

(* Pre: no additional constraints for `flip_case` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition is_lower (c : Z) : Prop :=
  97 <= c <= 122.

Definition is_upper (c : Z) : Prop :=
  65 <= c <= 90.

Definition flip_char (c : Z) : Z :=
  if (Z.leb 97 c) && (Z.leb c 122) then c - 32
  else if (Z.leb 65 c) && (Z.leb c 90) then c + 32
  else c.

Definition char_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition problem_27_pre (s : list Z) : Prop :=
  True.

Definition problem_27_spec (input output : list Z) : Prop :=
  ((String.length ((string_of_list input)) = String.length ((string_of_list output)) /\
    (forall (i : nat) (c : ascii),
      i < String.length ((string_of_list input)) ->
      String.get i ((string_of_list input)) = Some c ->
      (IsLow c -> String.get i ((string_of_list output)) = Some (Upper c)) /\
      (IsUp c -> String.get i ((string_of_list output)) = Some (Lower c)) /\
      (~IsLow c /\ ~IsUp c -> String.get i ((string_of_list output)) = Some c)))%nat).