Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.
From SimpleC.SL Require Import IntLib.
Import ListNotations.

Local Open Scope Z_scope.

Definition zsum_3 (l : list Z) : Z :=
  fold_left Z.add l 0.

Definition below_zero_prefix_safe (l : list Z) : Prop :=
  forall k,
    0 <= k < Zlength l ->
    INT_MIN <= zsum_3 (sublist 0 (k + 1) l) <= INT_MAX.

Definition problem_3_spec (l : list Z) (result : Z) : Prop :=
  (result <> 0 /\
   exists k, 0 <= k < Zlength l /\ zsum_3 (sublist 0 (k + 1) l) < 0) \/
  (result = 0 /\
   forall k, 0 <= k < Zlength l -> 0 <= zsum_3 (sublist 0 (k + 1) l)).
