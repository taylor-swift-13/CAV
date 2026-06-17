Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p128_prod_signs Require Import p128_prod_signs_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import p128_prod_signs.
Local Open Scope sac.

Lemma proof_of_abs_return_wit_1 : abs_return_wit_1.
Proof.
  pre_process.
Qed. 

Lemma proof_of_abs_return_wit_2 : abs_return_wit_2.
Proof.
  pre_process.
Qed. 

Lemma proof_of_p128_prod_signs_safety_wit_13 : p128_prod_signs_safety_wit_13.
Proof.
  pre_process.
  pose proof (prod_signs_prefix_prod_bound _ _ _ _ H9).
  entailer!.
Qed. 

Lemma proof_of_p128_prod_signs_safety_wit_17 : p128_prod_signs_safety_wit_17.
Proof.
  pre_process.
  pose proof (prod_signs_prefix_sum_range _ _ _ _ H8 H5) as Hsum.
  pose proof (prod_signs_prefix_prod_bound _ _ _ _ H8) as Hprod.
  entailer!.
  all: nia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_1 : p128_prod_signs_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  apply prod_signs_prefix_init.
  lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_2 : p128_prod_signs_entail_wit_2.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength input_l) by lia.
  pose proof (prod_signs_input_int_range input_l i H6 Hi) as Hcurrent.
  pose proof (prod_signs_next_sum_range i input_l sum prods (Znth i input_l 0) retval H9 H6 Hi eq_refl H) as Hnext.
  entailer!.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_1 : p128_prod_signs_entail_wit_3_1.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  apply prod_signs_prefix_neg with (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_2 : p128_prod_signs_entail_wit_3_2.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  apply prod_signs_prefix_pos with (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_entail_wit_3_3 : p128_prod_signs_entail_wit_3_3.
Proof.
  pre_process.
  subst current.
  subst mag.
  entailer!.
  eapply prod_signs_prefix_zero with (prods := prods) (x := Znth i input_l 0); try assumption; lia.
Qed. 

Lemma proof_of_p128_prod_signs_return_wit_1 : p128_prod_signs_return_wit_1.
Proof.
  pre_process.
  replace i with arr_size_pre in * by lia.
  entailer!.
  apply problem_128_spec_nonempty with (sum := sum) (prods := prods).
  - lia.
  - replace (Zlength input_l) with arr_size_pre by lia.
    assumption.
Qed. 

Lemma proof_of_p128_prod_signs_return_wit_2 : p128_prod_signs_return_wit_2.
Proof.
  pre_process.
  entailer!.
  apply problem_128_spec_empty.
  lia.
Qed. 

Lemma proof_of_p128_prod_signs_partial_solve_wit_2_pure : p128_prod_signs_partial_solve_wit_2_pure.
Proof.
  pre_process.
  assert (Hi : 0 <= i < Zlength input_l) by lia.
  pose proof (prod_signs_input_int_range input_l i H5 Hi) as Hcurrent.
  entailer!.
Qed. 
