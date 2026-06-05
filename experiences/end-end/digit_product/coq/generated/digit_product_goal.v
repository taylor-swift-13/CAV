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
Require Import digit_product.
Require Import digit_product_helper.
Local Open Scope sac.

(*----- Function digit_product -----*)

Definition digit_product_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digit_product_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digit_product_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition digit_product_safety_wit_4 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> product)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition digit_product_safety_wit_5 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> product)
|--
  “ ((product * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (product * (n % ( 10 ) ) )) ”
.

Definition digit_product_safety_wit_6 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> product)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digit_product_safety_wit_7 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> product)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digit_product_safety_wit_8 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> (product * (n % ( 10 ) ) ))
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition digit_product_safety_wit_9 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "product" ) )) # Int  |-> (product * (n % ( 10 ) ) ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition digit_product_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (digit_product_safe_z n_pre 1 ) ” 
  &&  “ ((digit_product_acc_z (n_pre) (1)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
.

Definition digit_product_entail_wit_2 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
|--
  “ (0 <= (n ÷ 10 )) ” 
  &&  “ (0 <= (product * (n % ( 10 ) ) )) ” 
  &&  “ (digit_product_safe_z (n ÷ 10 ) (product * (n % ( 10 ) ) ) ) ” 
  &&  “ ((digit_product_acc_z ((n ÷ 10 )) ((product * (n % ( 10 ) ) ))) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
.

Definition digit_product_return_wit_1 := 
forall (n_pre: Z) (product: Z) (n: Z) ,
  “ (n <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= product) ” 
  &&  “ (digit_product_safe_z n product ) ” 
  &&  “ ((digit_product_acc_z (n) (product)) = (digit_product_z (n_pre))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
|--
  “ (product = (digit_product_z (n_pre))) ”
  &&  emp
.

Definition digit_product_return_wit_2 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (digit_product_pre_z n_pre ) ”
  &&  emp
|--
  “ (0 = (digit_product_z (n_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_digit_product_safety_wit_1 : digit_product_safety_wit_1.
Axiom proof_of_digit_product_safety_wit_2 : digit_product_safety_wit_2.
Axiom proof_of_digit_product_safety_wit_3 : digit_product_safety_wit_3.
Axiom proof_of_digit_product_safety_wit_4 : digit_product_safety_wit_4.
Axiom proof_of_digit_product_safety_wit_5 : digit_product_safety_wit_5.
Axiom proof_of_digit_product_safety_wit_6 : digit_product_safety_wit_6.
Axiom proof_of_digit_product_safety_wit_7 : digit_product_safety_wit_7.
Axiom proof_of_digit_product_safety_wit_8 : digit_product_safety_wit_8.
Axiom proof_of_digit_product_safety_wit_9 : digit_product_safety_wit_9.
Axiom proof_of_digit_product_entail_wit_1 : digit_product_entail_wit_1.
Axiom proof_of_digit_product_entail_wit_2 : digit_product_entail_wit_2.
Axiom proof_of_digit_product_return_wit_1 : digit_product_return_wit_1.
Axiom proof_of_digit_product_return_wit_2 : digit_product_return_wit_2.

End VC_Correct.
