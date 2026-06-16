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
Require Import p138_is_equal_to_sum_even.
Local Open Scope sac.

(*----- Function p138_is_equal_to_sum_even -----*)

Definition p138_is_equal_to_sum_even_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_4 := 
forall (n_pre: Z) ,
  “ ((n_pre % ( 2 ) ) = 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_5 := 
forall (n_pre: Z) ,
  “ (n_pre >= 8) ” 
  &&  “ ((n_pre % ( 2 ) ) = 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_6 := 
forall (n_pre: Z) ,
  “ (n_pre < 8) ” 
  &&  “ ((n_pre % ( 2 ) ) = 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p138_is_equal_to_sum_even_safety_wit_7 := 
forall (n_pre: Z) ,
  “ ((n_pre % ( 2 ) ) <> 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p138_is_equal_to_sum_even_return_wit_1 := 
forall (n_pre: Z) ,
  “ ((n_pre % ( 2 ) ) <> 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (problem_138_spec n_pre 0 ) ”
  &&  emp
.

Definition p138_is_equal_to_sum_even_return_wit_2 := 
forall (n_pre: Z) ,
  “ (n_pre < 8) ” 
  &&  “ ((n_pre % ( 2 ) ) = 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (problem_138_spec n_pre 0 ) ”
  &&  emp
.

Definition p138_is_equal_to_sum_even_return_wit_3 := 
forall (n_pre: Z) ,
  “ (n_pre >= 8) ” 
  &&  “ ((n_pre % ( 2 ) ) = 0) ” 
  &&  “ (INT_MIN <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (problem_138_spec n_pre 1 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_1 : p138_is_equal_to_sum_even_safety_wit_1.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_2 : p138_is_equal_to_sum_even_safety_wit_2.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_3 : p138_is_equal_to_sum_even_safety_wit_3.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_4 : p138_is_equal_to_sum_even_safety_wit_4.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_5 : p138_is_equal_to_sum_even_safety_wit_5.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_6 : p138_is_equal_to_sum_even_safety_wit_6.
Axiom proof_of_p138_is_equal_to_sum_even_safety_wit_7 : p138_is_equal_to_sum_even_safety_wit_7.
Axiom proof_of_p138_is_equal_to_sum_even_return_wit_1 : p138_is_equal_to_sum_even_return_wit_1.
Axiom proof_of_p138_is_equal_to_sum_even_return_wit_2 : p138_is_equal_to_sum_even_return_wit_2.
Axiom proof_of_p138_is_equal_to_sum_even_return_wit_3 : p138_is_equal_to_sum_even_return_wit_3.

End VC_Correct.
