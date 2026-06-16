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
Require Import p073_smallest_change.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p073_smallest_change -----*)

Definition p073_smallest_change_safety_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "out" ) )) # Int  |->_)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p073_smallest_change_safety_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Int  |-> 0)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size_pre)
  **  ((( &( "arr" ) )) # Ptr  |-> arr_pre)
  **  (IntArray.full arr_pre arr_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p073_smallest_change_safety_wit_3 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ ((arr_size <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p073_smallest_change_safety_wit_4 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p073_smallest_change_safety_wit_5 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (((arr_size - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size - 1 ) - i )) ”
.

Definition p073_smallest_change_safety_wit_6 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ ((arr_size - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size - 1 )) ”
.

Definition p073_smallest_change_safety_wit_7 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p073_smallest_change_safety_wit_8 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p073_smallest_change_safety_wit_9 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 > ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ False ”
.

Definition p073_smallest_change_safety_wit_10 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (((arr_size - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size - 1 ) - i )) ”
.

Definition p073_smallest_change_safety_wit_11 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ ((arr_size - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size - 1 )) ”
.

Definition p073_smallest_change_safety_wit_12 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p073_smallest_change_safety_wit_13 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) >= arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
  **  (IntArray.full arr arr_size lv )
|--
  “ False ”
.

Definition p073_smallest_change_safety_wit_14 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ (((arr_size - 1 ) - i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((arr_size - 1 ) - i )) ”
.

Definition p073_smallest_change_safety_wit_15 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ ((arr_size - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (arr_size - 1 )) ”
.

Definition p073_smallest_change_safety_wit_16 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p073_smallest_change_safety_wit_17 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) <> (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ ((out + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (out + 1 )) ”
.

Definition p073_smallest_change_safety_wit_18 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) <> (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p073_smallest_change_safety_wit_19 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) = (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> out)
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p073_smallest_change_safety_wit_20 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) <> (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "arr_size" ) )) # Int  |-> arr_size)
  **  ((( &( "out" ) )) # Int  |-> (out + 1 ))
  **  ((( &( "arr" ) )) # Ptr  |-> arr)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p073_smallest_change_entail_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) ,
  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr_pre arr_size_pre lv )
|--
  “ (0 <= 0) ” 
  &&  “ ((2 * 0 ) <= arr_size_pre) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (0 = (count_half_mismatches_upto (0) (lv))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition p073_smallest_change_entail_wit_2_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) <> (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= arr_size) ” 
  &&  “ ((i + 1 ) <= arr_size) ” 
  &&  “ ((out + 1 ) = (count_half_mismatches_upto ((i + 1 )) (lv))) ” 
  &&  “ (INT_MIN <= (out + 1 )) ” 
  &&  “ ((out + 1 ) <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
.

Definition p073_smallest_change_entail_wit_2_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ ((Znth i lv 0) = (Znth ((arr_size - 1 ) - i ) lv 0)) ” 
  &&  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= arr_size) ” 
  &&  “ ((i + 1 ) <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto ((i + 1 )) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
.

Definition p073_smallest_change_return_wit_1 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i >= (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (problem_73_spec lv out ) ”
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition p073_smallest_change_return_wit_2 := 
forall (arr_size_pre: Z) (arr_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (i >= arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (problem_73_spec lv out ) ”
  &&  (IntArray.full arr_pre arr_size_pre lv )
.

Definition p073_smallest_change_partial_solve_wit_1 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (((arr + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i arr i 0 arr_size lv )
.

Definition p073_smallest_change_partial_solve_wit_2 := 
forall (arr_size_pre: Z) (lv: (@list Z)) (arr: Z) (out: Z) (arr_size: Z) (i: Z) ,
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (IntArray.full arr arr_size lv )
|--
  “ (((arr_size - 1 ) - i ) < arr_size) ” 
  &&  “ (0 <= ((arr_size - 1 ) - i )) ” 
  &&  “ (i < arr_size) ” 
  &&  “ (i < (arr_size ÷ 2 )) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= arr_size) ” 
  &&  “ (i <= arr_size) ” 
  &&  “ (out = (count_half_mismatches_upto (i) (lv))) ” 
  &&  “ (INT_MIN <= out) ” 
  &&  “ (out <= INT_MAX) ” 
  &&  “ (0 <= arr_size_pre) ” 
  &&  “ (arr_size_pre < INT_MAX) ” 
  &&  “ (arr_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_73_pre lv ) ” 
  &&  “ (smallest_change_int_range lv ) ”
  &&  (((arr + (((arr_size - 1 ) - i ) * sizeof(INT) ) )) # Int  |-> (Znth ((arr_size - 1 ) - i ) lv 0))
  **  (IntArray.missing_i arr ((arr_size - 1 ) - i ) 0 arr_size lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p073_smallest_change_safety_wit_1 : p073_smallest_change_safety_wit_1.
Axiom proof_of_p073_smallest_change_safety_wit_2 : p073_smallest_change_safety_wit_2.
Axiom proof_of_p073_smallest_change_safety_wit_3 : p073_smallest_change_safety_wit_3.
Axiom proof_of_p073_smallest_change_safety_wit_4 : p073_smallest_change_safety_wit_4.
Axiom proof_of_p073_smallest_change_safety_wit_5 : p073_smallest_change_safety_wit_5.
Axiom proof_of_p073_smallest_change_safety_wit_6 : p073_smallest_change_safety_wit_6.
Axiom proof_of_p073_smallest_change_safety_wit_7 : p073_smallest_change_safety_wit_7.
Axiom proof_of_p073_smallest_change_safety_wit_8 : p073_smallest_change_safety_wit_8.
Axiom proof_of_p073_smallest_change_safety_wit_9 : p073_smallest_change_safety_wit_9.
Axiom proof_of_p073_smallest_change_safety_wit_10 : p073_smallest_change_safety_wit_10.
Axiom proof_of_p073_smallest_change_safety_wit_11 : p073_smallest_change_safety_wit_11.
Axiom proof_of_p073_smallest_change_safety_wit_12 : p073_smallest_change_safety_wit_12.
Axiom proof_of_p073_smallest_change_safety_wit_13 : p073_smallest_change_safety_wit_13.
Axiom proof_of_p073_smallest_change_safety_wit_14 : p073_smallest_change_safety_wit_14.
Axiom proof_of_p073_smallest_change_safety_wit_15 : p073_smallest_change_safety_wit_15.
Axiom proof_of_p073_smallest_change_safety_wit_16 : p073_smallest_change_safety_wit_16.
Axiom proof_of_p073_smallest_change_safety_wit_17 : p073_smallest_change_safety_wit_17.
Axiom proof_of_p073_smallest_change_safety_wit_18 : p073_smallest_change_safety_wit_18.
Axiom proof_of_p073_smallest_change_safety_wit_19 : p073_smallest_change_safety_wit_19.
Axiom proof_of_p073_smallest_change_safety_wit_20 : p073_smallest_change_safety_wit_20.
Axiom proof_of_p073_smallest_change_entail_wit_1 : p073_smallest_change_entail_wit_1.
Axiom proof_of_p073_smallest_change_entail_wit_2_1 : p073_smallest_change_entail_wit_2_1.
Axiom proof_of_p073_smallest_change_entail_wit_2_2 : p073_smallest_change_entail_wit_2_2.
Axiom proof_of_p073_smallest_change_return_wit_1 : p073_smallest_change_return_wit_1.
Axiom proof_of_p073_smallest_change_return_wit_2 : p073_smallest_change_return_wit_2.
Axiom proof_of_p073_smallest_change_partial_solve_wit_1 : p073_smallest_change_partial_solve_wit_1.
Axiom proof_of_p073_smallest_change_partial_solve_wit_2 : p073_smallest_change_partial_solve_wit_2.

End VC_Correct.
