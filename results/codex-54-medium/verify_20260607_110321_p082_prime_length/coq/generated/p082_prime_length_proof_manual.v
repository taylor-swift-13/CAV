Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.verify_20260607_110321_p082_prime_length Require Import p082_prime_length_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p082_prime_length.
Local Open Scope sac.

Lemma prime_prefix_succ :
  forall i n,
    prime_prefix i n ->
    Z.rem n i <> 0 ->
    prime_prefix (i + 1) n.
Proof.
  unfold prime_prefix.
  intros i n Hprefix Hrem d Hd.
  assert (d < i \/ d = i) by lia.
  destruct H as [Hlt | Heq].
  - apply Hprefix; lia.
  - subst d; exact Hrem.
Qed.

Lemma prime_prefix_implies_prime_len :
  forall i n,
    2 <= i ->
    2 <= n ->
    i * i > n ->
    prime_prefix i n ->
    prime_len n.
Proof.
  intros i n Hi Hn Hbound Hprefix.
  unfold prime_len, prime_prefix in *.
  split; [exact Hn|].
  intros d [Hd2 HdSq].
  apply Hprefix.
  assert (d < i) by nia.
  lia.
Qed.

Lemma proof_of_p082_prime_length_safety_wit_4 : p082_prime_length_safety_wit_4.
Proof.
  pre_process.
Qed.

Lemma proof_of_p082_prime_length_entail_wit_1 : p082_prime_length_entail_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - subst retval. cancel.
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial.
      lia.
    + dump_pre_spatial.
      unfold prime_prefix.
      intros d Hd.
      lia.
    + dump_pre_spatial. auto.
Qed.

Lemma proof_of_p082_prime_length_entail_wit_2 : p082_prime_length_entail_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial. nia.
    + dump_pre_spatial.
      eapply prime_prefix_succ; eauto.
    + dump_pre_spatial. auto.
Qed.

Lemma proof_of_p082_prime_length_return_wit_1 : p082_prime_length_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial.
      unfold problem_82_spec, bool_of.
      split.
      * intros _.
        match goal with
        | Hlen_eq : Zlength l = len |- _ => rewrite Hlen_eq
        end.
        eapply prime_prefix_implies_prime_len.
        -- exact H4.
        -- exact H2.
        -- exact H.
        -- exact H7.
      * intros _. reflexivity.
Qed.

Lemma proof_of_p082_prime_length_return_wit_2 : p082_prime_length_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial.
      unfold problem_82_spec, bool_of.
      split.
      * intros Hspec. discriminate Hspec.
      * intros Hspec.
        match goal with
        | Hlen_eq : Zlength l = len |- _ => rewrite Hlen_eq in Hspec
        end.
        destruct Hspec as [_ Hprime].
        specialize (Hprime i).
        assert (Hdiv_range : 2 <= i /\ i * i <= len) by lia.
        specialize (Hprime Hdiv_range).
        contradiction.
Qed.

Lemma proof_of_p082_prime_length_return_wit_3 : p082_prime_length_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel (CharArray.full str_pre (len + 1) (app l (cons 0 nil))).
  - split_pures.
    + dump_pre_spatial. auto.
    + dump_pre_spatial.
      unfold problem_82_spec, bool_of.
      split.
      * intros Hspec. discriminate Hspec.
      * intros Hspec.
        match goal with
        | Hlen_eq : Zlength l = len |- _ => rewrite Hlen_eq in Hspec
        end.
        destruct Hspec as [Hlen _].
        lia.
Qed.
