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
Require Import add_digits.
Local Open Scope sac.

(*----- Function add_digits -----*)

Definition add_digits_safety_wit_1 := 
forall (num_pre: Z) (num: Z) ,
  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ ((digital_root_z (num)) = (digital_root_z (num_pre))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition add_digits_safety_wit_2 := 
forall (num_pre: Z) (num: Z) ,
  “ (num >= 10) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ ((digital_root_z (num)) = (digital_root_z (num_pre))) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_digits_safety_wit_3 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition add_digits_safety_wit_4 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (num % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (num % ( 10 ) ) )) ”
.

Definition add_digits_safety_wit_5 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((num <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition add_digits_safety_wit_6 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition add_digits_safety_wit_7 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (num % ( 10 ) ) ))
|--
  “ ((num <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition add_digits_safety_wit_8 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (num % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition add_digits_entail_wit_1 := 
forall (num_pre: Z) ,
  “ (0 <= num_pre) ”
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
|--
  “ (num_pre <= INT_MAX) ” 
  &&  “ (0 <= num_pre) ”
  &&  ((( &( "num" ) )) # Int  |-> num_pre)
.

Definition add_digits_entail_wit_2 := 
forall (num_pre: Z) ,
  “ (num_pre <= INT_MAX) ” 
  &&  “ (0 <= num_pre) ”
  &&  emp
|--
  “ (0 <= num_pre) ” 
  &&  “ (num_pre <= INT_MAX) ” 
  &&  “ ((digital_root_z (num_pre)) = (digital_root_z (num_pre))) ”
  &&  emp
.

Definition add_digits_entail_wit_3 := 
forall (num_pre: Z) (num: Z) ,
  “ (num >= 10) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ ((digital_root_z (num)) = (digital_root_z (num_pre))) ”
  &&  emp
|--
  EX (n0: Z) ,
  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((0 + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  emp
.

Definition add_digits_entail_wit_4 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0_2: Z) ,
  “ (num > 0) ” 
  &&  “ (0 <= n0_2) ” 
  &&  “ (n0_2 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0_2)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0_2))) ”
  &&  emp
|--
  EX (n0: Z) ,
  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= (num ÷ 10 )) ” 
  &&  “ ((num ÷ 10 ) <= INT_MAX) ” 
  &&  “ (0 <= (sum + (num % ( 10 ) ) )) ” 
  &&  “ ((sum + (num % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ (((sum + (num % ( 10 ) ) ) + (digit_sum_z ((num ÷ 10 ))) ) = (digit_sum_z (n0))) ”
  &&  emp
.

Definition add_digits_entail_wit_5 := 
forall (num_pre: Z) (sum: Z) (num: Z) (n0: Z) ,
  “ (num <= 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 <= INT_MAX) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (n0)) = (digital_root_z (num_pre))) ” 
  &&  “ ((sum + (digit_sum_z (num)) ) = (digit_sum_z (n0))) ”
  &&  emp
|--
  “ (0 <= sum) ” 
  &&  “ (sum <= INT_MAX) ” 
  &&  “ ((digital_root_z (sum)) = (digital_root_z (num_pre))) ”
  &&  emp
.

Definition add_digits_return_wit_1 := 
forall (num_pre: Z) (num: Z) ,
  “ (num < 10) ” 
  &&  “ (0 <= num) ” 
  &&  “ (num <= INT_MAX) ” 
  &&  “ ((digital_root_z (num)) = (digital_root_z (num_pre))) ”
  &&  emp
|--
  “ (num = (digital_root_z (num_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_add_digits_safety_wit_1 : add_digits_safety_wit_1.
Axiom proof_of_add_digits_safety_wit_2 : add_digits_safety_wit_2.
Axiom proof_of_add_digits_safety_wit_3 : add_digits_safety_wit_3.
Axiom proof_of_add_digits_safety_wit_4 : add_digits_safety_wit_4.
Axiom proof_of_add_digits_safety_wit_5 : add_digits_safety_wit_5.
Axiom proof_of_add_digits_safety_wit_6 : add_digits_safety_wit_6.
Axiom proof_of_add_digits_safety_wit_7 : add_digits_safety_wit_7.
Axiom proof_of_add_digits_safety_wit_8 : add_digits_safety_wit_8.
Axiom proof_of_add_digits_entail_wit_1 : add_digits_entail_wit_1.
Axiom proof_of_add_digits_entail_wit_2 : add_digits_entail_wit_2.
Axiom proof_of_add_digits_entail_wit_3 : add_digits_entail_wit_3.
Axiom proof_of_add_digits_entail_wit_4 : add_digits_entail_wit_4.
Axiom proof_of_add_digits_entail_wit_5 : add_digits_entail_wit_5.
Axiom proof_of_add_digits_return_wit_1 : add_digits_return_wit_1.

End VC_Correct.
