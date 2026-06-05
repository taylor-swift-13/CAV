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
Require Import array_sum_positive.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_sum_positive -----*)

Definition array_sum_positive_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_sum_positive_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_sum_positive_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_sum_positive_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i l 0) )) ”
.

Definition array_sum_positive_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) <= 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_sum_positive_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_sum_positive_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (array_sum_positive_spec ((sublist (0) (0) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_positive_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (sum + (Znth i l 0) )) ” 
  &&  “ ((sum + (Znth i l 0) ) = (array_sum_positive_spec ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_positive_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) <= 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_positive_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (sum = (array_sum_positive_spec (l))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_sum_positive_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_sum_positive_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i l 0) > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ ((Znth i l 0) > 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum = (array_sum_positive_spec ((sublist (0) (i) (l))))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (array_sum_positive_spec (l))) ” 
  &&  “ ((array_sum_positive_spec (l)) <= INT_MAX) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_sum_positive_safety_wit_1 : array_sum_positive_safety_wit_1.
Axiom proof_of_array_sum_positive_safety_wit_2 : array_sum_positive_safety_wit_2.
Axiom proof_of_array_sum_positive_safety_wit_3 : array_sum_positive_safety_wit_3.
Axiom proof_of_array_sum_positive_safety_wit_4 : array_sum_positive_safety_wit_4.
Axiom proof_of_array_sum_positive_safety_wit_5 : array_sum_positive_safety_wit_5.
Axiom proof_of_array_sum_positive_safety_wit_6 : array_sum_positive_safety_wit_6.
Axiom proof_of_array_sum_positive_entail_wit_1 : array_sum_positive_entail_wit_1.
Axiom proof_of_array_sum_positive_entail_wit_2_1 : array_sum_positive_entail_wit_2_1.
Axiom proof_of_array_sum_positive_entail_wit_2_2 : array_sum_positive_entail_wit_2_2.
Axiom proof_of_array_sum_positive_return_wit_1 : array_sum_positive_return_wit_1.
Axiom proof_of_array_sum_positive_partial_solve_wit_1 : array_sum_positive_partial_solve_wit_1.
Axiom proof_of_array_sum_positive_partial_solve_wit_2 : array_sum_positive_partial_solve_wit_2.

End VC_Correct.
