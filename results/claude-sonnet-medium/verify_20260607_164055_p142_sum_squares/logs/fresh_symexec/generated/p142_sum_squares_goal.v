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
Require Import p142_sum_squares.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p142_sum_squares -----*)

Definition p142_sum_squares_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre input_l ) ” 
  &&  “ (sum_squares_int_range input_l ) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p142_sum_squares_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre input_l ) ” 
  &&  “ (sum_squares_int_range input_l ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p142_sum_squares_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition p142_sum_squares_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p142_sum_squares_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p142_sum_squares_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) )) ”
.

Definition p142_sum_squares_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
.

Definition p142_sum_squares_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i <> (INT_MIN)) \/ (4 <> (-1))) ” 
  &&  “ (4 <> 0) ”
.

Definition p142_sum_squares_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition p142_sum_squares_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p142_sum_squares_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) )) ”
.

Definition p142_sum_squares_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) )) ”
.

Definition p142_sum_squares_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (((Znth i input_l 0) * (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) * (Znth i input_l 0) )) ”
.

Definition p142_sum_squares_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i input_l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p142_sum_squares_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p142_sum_squares_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p142_sum_squares_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i input_l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i input_l 0) )) ”
.

Definition p142_sum_squares_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_142_pre input_l ) ” 
  &&  “ (sum_squares_int_range input_l ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (0 = (transformed_prefix_sum (0) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition p142_sum_squares_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ ((sum + ((Znth i input_l 0) * (Znth i input_l 0) ) ) = (transformed_prefix_sum ((i + 1 )) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition p142_sum_squares_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ ((sum + (((Znth i input_l 0) * (Znth i input_l 0) ) * (Znth i input_l 0) ) ) = (transformed_prefix_sum ((i + 1 )) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition p142_sum_squares_entail_wit_2_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ ((sum + (Znth i input_l 0) ) = (transformed_prefix_sum ((i + 1 )) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition p142_sum_squares_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i >= lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ (problem_142_spec input_l sum ) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 3 ) ) = 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) = 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Definition p142_sum_squares_partial_solve_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (input_l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (IntArray.full lst_pre lst_size_pre input_l )
|--
  “ ((i % ( 4 ) ) <> 0) ” 
  &&  “ ((i % ( 3 ) ) <> 0) ” 
  &&  “ (i < lst_size_pre) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (input_l))) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= lst_size_pre) ” 
  &&  “ (sum_squares_int_range input_l ) ” 
  &&  “ (sum = (transformed_prefix_sum (i) (input_l))) ”
  &&  (((lst_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i lst_pre i 0 lst_size_pre input_l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p142_sum_squares_safety_wit_1 : p142_sum_squares_safety_wit_1.
Axiom proof_of_p142_sum_squares_safety_wit_2 : p142_sum_squares_safety_wit_2.
Axiom proof_of_p142_sum_squares_safety_wit_3 : p142_sum_squares_safety_wit_3.
Axiom proof_of_p142_sum_squares_safety_wit_4 : p142_sum_squares_safety_wit_4.
Axiom proof_of_p142_sum_squares_safety_wit_5 : p142_sum_squares_safety_wit_5.
Axiom proof_of_p142_sum_squares_safety_wit_6 : p142_sum_squares_safety_wit_6.
Axiom proof_of_p142_sum_squares_safety_wit_7 : p142_sum_squares_safety_wit_7.
Axiom proof_of_p142_sum_squares_safety_wit_8 : p142_sum_squares_safety_wit_8.
Axiom proof_of_p142_sum_squares_safety_wit_9 : p142_sum_squares_safety_wit_9.
Axiom proof_of_p142_sum_squares_safety_wit_10 : p142_sum_squares_safety_wit_10.
Axiom proof_of_p142_sum_squares_safety_wit_11 : p142_sum_squares_safety_wit_11.
Axiom proof_of_p142_sum_squares_safety_wit_12 : p142_sum_squares_safety_wit_12.
Axiom proof_of_p142_sum_squares_safety_wit_13 : p142_sum_squares_safety_wit_13.
Axiom proof_of_p142_sum_squares_safety_wit_14 : p142_sum_squares_safety_wit_14.
Axiom proof_of_p142_sum_squares_safety_wit_15 : p142_sum_squares_safety_wit_15.
Axiom proof_of_p142_sum_squares_safety_wit_16 : p142_sum_squares_safety_wit_16.
Axiom proof_of_p142_sum_squares_safety_wit_17 : p142_sum_squares_safety_wit_17.
Axiom proof_of_p142_sum_squares_entail_wit_1 : p142_sum_squares_entail_wit_1.
Axiom proof_of_p142_sum_squares_entail_wit_2_1 : p142_sum_squares_entail_wit_2_1.
Axiom proof_of_p142_sum_squares_entail_wit_2_2 : p142_sum_squares_entail_wit_2_2.
Axiom proof_of_p142_sum_squares_entail_wit_2_3 : p142_sum_squares_entail_wit_2_3.
Axiom proof_of_p142_sum_squares_return_wit_1 : p142_sum_squares_return_wit_1.
Axiom proof_of_p142_sum_squares_partial_solve_wit_1 : p142_sum_squares_partial_solve_wit_1.
Axiom proof_of_p142_sum_squares_partial_solve_wit_2 : p142_sum_squares_partial_solve_wit_2.
Axiom proof_of_p142_sum_squares_partial_solve_wit_3 : p142_sum_squares_partial_solve_wit_3.
Axiom proof_of_p142_sum_squares_partial_solve_wit_4 : p142_sum_squares_partial_solve_wit_4.
Axiom proof_of_p142_sum_squares_partial_solve_wit_5 : p142_sum_squares_partial_solve_wit_5.
Axiom proof_of_p142_sum_squares_partial_solve_wit_6 : p142_sum_squares_partial_solve_wit_6.

End VC_Correct.
