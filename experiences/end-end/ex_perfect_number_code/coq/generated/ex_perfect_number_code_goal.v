Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import ex_perfect_number_code.
Require Import ex_perfect_number_code_helper.
Local Open Scope sac.

(*----- Function ex_perfect_number_code -----*)

Definition ex_perfect_number_code_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_perfect_number_code_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_perfect_number_code_safety_wit_3 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((n_pre <> (INT_MIN)) \/ (d <> (-1))) ” 
  &&  “ (d <> 0) ”
.

Definition ex_perfect_number_code_safety_wit_4 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_perfect_number_code_safety_wit_5 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ ((n_pre % ( d ) ) = 0) ” 
  &&  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + d )) ”
.

Definition ex_perfect_number_code_safety_wit_6 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ ((n_pre % ( d ) ) <> 0) ” 
  &&  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition ex_perfect_number_code_safety_wit_7 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ ((n_pre % ( d ) ) = 0) ” 
  &&  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "sum" ) )) # Int  |-> (sum + d ))
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition ex_perfect_number_code_safety_wit_8 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum = n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_perfect_number_code_safety_wit_9 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum > n_pre) ” 
  &&  “ (sum <> n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_perfect_number_code_safety_wit_10 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum <= n_pre) ” 
  &&  “ (sum <> n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition ex_perfect_number_code_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  “ (0 < n_pre) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (1))) ” 
  &&  “ ((0 + (aliquot_sum_tail_z (n_pre) (1)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
.

Definition ex_perfect_number_code_entail_wit_2_1 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ ((n_pre % ( d ) ) = 0) ” 
  &&  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  “ (0 < n_pre) ” 
  &&  “ (1 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= n_pre) ” 
  &&  “ (0 <= (sum + d )) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) ((d + 1 )))) ” 
  &&  “ (((sum + d ) + (aliquot_sum_tail_z (n_pre) ((d + 1 ))) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
.

Definition ex_perfect_number_code_entail_wit_2_2 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ ((n_pre % ( d ) ) <> 0) ” 
  &&  “ (d < n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  “ (0 < n_pre) ” 
  &&  “ (1 <= (d + 1 )) ” 
  &&  “ ((d + 1 ) <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) ((d + 1 )))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) ((d + 1 ))) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
.

Definition ex_perfect_number_code_entail_wit_3 := 
forall (n_pre: Z) (sum: Z) (d: Z) ,
  “ (d >= n_pre) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ (1 <= d) ” 
  &&  “ (d <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (0 <= (aliquot_sum_tail_z (n_pre) (d))) ” 
  &&  “ ((sum + (aliquot_sum_tail_z (n_pre) (d)) ) = (aliquot_sum_z (n_pre))) ” 
  &&  “ (0 < n_pre) ” 
  &&  “ ((aliquot_sum_z (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  emp
.

Definition ex_perfect_number_code_return_wit_1 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum <= n_pre) ” 
  &&  “ (sum <> n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  emp
|--
  “ (ex_perfect_number_code_spec n_pre 3 ) ”
  &&  emp
.

Definition ex_perfect_number_code_return_wit_2 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum > n_pre) ” 
  &&  “ (sum <> n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  emp
|--
  “ (ex_perfect_number_code_spec n_pre 2 ) ”
  &&  emp
.

Definition ex_perfect_number_code_return_wit_3 := 
forall (n_pre: Z) (sum: Z) ,
  “ (sum = n_pre) ” 
  &&  “ (sum = (aliquot_sum_z (n_pre))) ”
  &&  emp
|--
  “ (ex_perfect_number_code_spec n_pre 1 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_perfect_number_code_safety_wit_1 : ex_perfect_number_code_safety_wit_1.
Axiom proof_of_ex_perfect_number_code_safety_wit_2 : ex_perfect_number_code_safety_wit_2.
Axiom proof_of_ex_perfect_number_code_safety_wit_3 : ex_perfect_number_code_safety_wit_3.
Axiom proof_of_ex_perfect_number_code_safety_wit_4 : ex_perfect_number_code_safety_wit_4.
Axiom proof_of_ex_perfect_number_code_safety_wit_5 : ex_perfect_number_code_safety_wit_5.
Axiom proof_of_ex_perfect_number_code_safety_wit_6 : ex_perfect_number_code_safety_wit_6.
Axiom proof_of_ex_perfect_number_code_safety_wit_7 : ex_perfect_number_code_safety_wit_7.
Axiom proof_of_ex_perfect_number_code_safety_wit_8 : ex_perfect_number_code_safety_wit_8.
Axiom proof_of_ex_perfect_number_code_safety_wit_9 : ex_perfect_number_code_safety_wit_9.
Axiom proof_of_ex_perfect_number_code_safety_wit_10 : ex_perfect_number_code_safety_wit_10.
Axiom proof_of_ex_perfect_number_code_entail_wit_1 : ex_perfect_number_code_entail_wit_1.
Axiom proof_of_ex_perfect_number_code_entail_wit_2_1 : ex_perfect_number_code_entail_wit_2_1.
Axiom proof_of_ex_perfect_number_code_entail_wit_2_2 : ex_perfect_number_code_entail_wit_2_2.
Axiom proof_of_ex_perfect_number_code_entail_wit_3 : ex_perfect_number_code_entail_wit_3.
Axiom proof_of_ex_perfect_number_code_return_wit_1 : ex_perfect_number_code_return_wit_1.
Axiom proof_of_ex_perfect_number_code_return_wit_2 : ex_perfect_number_code_return_wit_2.
Axiom proof_of_ex_perfect_number_code_return_wit_3 : ex_perfect_number_code_return_wit_3.

End VC_Correct.
