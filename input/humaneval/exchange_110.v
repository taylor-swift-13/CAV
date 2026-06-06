(* spec/110 *)
(* 
In this problem, you will implement a function that takes two lists of numbers,
and determines whether it is possible to perform an exchange of elements
between them to make lst1 a list of only even numbers.
There is no limit on the number of exchanged elements between lst1 and lst2.
If it is possible to exchange elements between the lst1 and lst2 to make
all the elements of lst1 to be even, return "YES".
Otherwise, return "NO".
For example:
exchange([1, 2, 3, 4], [1, 2, 3, 4]) => "YES"
exchange([1, 2, 3, 4], [1, 5, 3, 4]) => "NO"
It is assumed that the input lists will be non-empty.
*)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* 两个输入列表均非空 *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
From AUXLib Require Import ListLib.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Definition yesno_of_110 (z : Z) : string :=
  if Z.eqb z 1 then "YES" else "NO".

Definition list_Z_to_nat_110 (l : list Z) : list nat :=
  map Z.to_nat l.

Definition nonnegative_list (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> 0 <= Znth i l 0.

Definition problem_110_pre (lst1 lst2 : list Z) : Prop :=
  lst1 <> [] /\ lst2 <> [].

Definition even_zb (x : Z) : bool :=
  Z.eqb (Z.rem x 2) 0.

Fixpoint count_even_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => (if even_zb x then 1 else 0) + count_even_list xs
  end.

Definition count_even_upto (i : Z) (l : list Z) : Z :=
  count_even_list (sublist 0 i l).

Definition problem_110_spec (lst1 lst2 : list Z) (output : Z) : Prop :=
  let odds_in_lst1 := Zlength lst1 - count_even_list lst1 in
  let evens_in_lst2 := count_even_list lst2 in
  if Z.leb odds_in_lst1 evens_in_lst2
  then yesno_of_110 output = "YES"%string
  else yesno_of_110 output = "NO"%string.
