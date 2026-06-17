(* spec/42 *)
(* Return list with elements incremented by 1.
>>> incr_list([1, 2, 3])
[2, 3, 4]
>>> incr_list([5, 3, 5, 2, 3, 3, 9, 0, 123])
[6, 4, 6, 3, 4, 4, 10, 1, 124] *)

(* Spec(input : list int, output : list int) :=
​	length(input) = length(output) /\
​	∀i ∈ [0, length(input)), outpu[i] = input[i] + 1
*)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
From AUXLib Require Import ListLib.
Import ListNotations.
Open Scope Z_scope.

(* Pre: no special constraints for `incr_list` *)
Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  Zlength input = Zlength output /\
  forall i, 0 <= i < Zlength output -> Znth i output 0 = Znth i input 0 + 1.

Require Import Coq.micromega.Lia.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.

Definition map_incr (l : list Z) : list Z :=
  map (fun x => x + 1) l.

Definition list_incr_int_range (l : list Z) : Prop :=
  forall i, 0 <= i < Zlength l -> INT_MIN <= Znth i l 0 + 1 <= INT_MAX.

Lemma map_incr_Zlength :
  forall l, Zlength (map_incr l) = Zlength l.
Proof.
  intros l.
  unfold map_incr.
  rewrite !Zlength_correct.
  rewrite length_map.
  reflexivity.
Qed.

Lemma map_incr_sublist_snoc :
  forall l i,
    0 <= i < Zlength l ->
    map_incr (sublist 0 (i + 1) l) =
      map_incr (sublist 0 i l) ++ [Znth i l 0 + 1].
Proof.
  intros l i Hi.
  unfold map_incr.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
  rewrite (sublist_single 0 i l) by lia.
  rewrite map_app.
  simpl.
  reflexivity.
Qed.

Lemma problem_42_spec_map_incr :
  forall input, problem_42_spec input (map_incr input).
Proof.
  intros input.
  unfold problem_42_spec, map_incr.
  split.
  - rewrite !Zlength_correct.
    rewrite length_map.
    reflexivity.
  - intros i Hi.
    unfold Znth.
    rewrite map_nth_len with (dy := 0).
    + reflexivity.
    + rewrite <- (Nat2Z.id (length input)).
      pose proof (Z2Nat.inj_lt i (Z.of_nat (length input)) ltac:(lia) ltac:(lia)) as Hlt.
      apply (proj1 Hlt).
      rewrite Zlength_correct in Hi.
      rewrite length_map in Hi.
      lia.
Qed.
