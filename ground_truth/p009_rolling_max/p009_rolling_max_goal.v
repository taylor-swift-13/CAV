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
Require Import p009_rolling_max.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p009_rolling_max -----*)

Definition p009_rolling_max_safety_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (out_pre = out0) ” 
  &&  “ (out_size_pre = out_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (problem_9_pre ) ” 
  &&  “ (list_int_range lv ) ”
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  “ (2147483648 <> (-9223372036854775808)) ”
.

Definition p009_rolling_max_safety_wit_2 := 
forall (out_size_pre: Z) (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (out_pre = out0) ” 
  &&  “ (out_size_pre = out_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (problem_9_pre ) ” 
  &&  “ (list_int_range lv ) ”
  &&  ((( &( "max" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  “ (2147483648 <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= 2147483648) ”
.

Definition p009_rolling_max_safety_wit_3 := 
forall (out_size_pre: Z) (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (out_pre = out0) ” 
  &&  “ (out_size_pre = out_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (problem_9_pre ) ” 
  &&  “ (list_int_range lv ) ”
  &&  ((( &( "max" ) )) # Int  |-> (INT_MIN))
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p009_rolling_max_safety_wit_4 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.seg out0 0 (i + 1 ) (app ((rolling_max_f (INT_MIN) ((sublist (0) (i) (lv))))) ((cons ((Znth i lv 0)) (nil)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> (Znth i lv 0))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p009_rolling_max_safety_wit_5 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) <= max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.seg out0 0 (i + 1 ) (app ((rolling_max_f (INT_MIN) ((sublist (0) (i) (lv))))) ((cons (max) (nil)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "max" ) )) # Int  |-> max)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p009_rolling_max_entail_wit_1 := 
forall (out_size_pre: Z) (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (out_pre = out0) ” 
  &&  “ (out_size_pre = out_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (problem_9_pre ) ” 
  &&  “ (list_int_range lv ) ”
  &&  ((( &( "out_size" ) )) # Int  |-> out_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full out_pre out_size_pre )
|--
  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ ((INT_MIN) = (running_max_val (INT_MIN) ((sublist (0) (0) (lv))))) ”
  &&  ((( &( "numbers" ) )) # Ptr  |-> numbers0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "out" ) )) # Ptr  |-> out0)
  **  ((( &( "out_size" ) )) # Int  |-> out_size0)
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 0 (rolling_max_f (INT_MIN) ((sublist (0) (0) (lv)))) )
  **  (IntArray.undef_seg out0 0 out_size0 )
.

Definition p009_rolling_max_entail_wit_2_1 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) <= max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.seg out0 0 (i + 1 ) (app ((rolling_max_f (INT_MIN) ((sublist (0) (i) (lv))))) ((cons (max) (nil)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
|--
  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) ((i + 1 )) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 (i + 1 ) (rolling_max_f (INT_MIN) ((sublist (0) ((i + 1 )) (lv)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
.

Definition p009_rolling_max_entail_wit_2_2 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.seg out0 0 (i + 1 ) (app ((rolling_max_f (INT_MIN) ((sublist (0) (i) (lv))))) ((cons ((Znth i lv 0)) (nil)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
|--
  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numbers_size0) ” 
  &&  “ ((Znth i lv 0) = (running_max_val (INT_MIN) ((sublist (0) ((i + 1 )) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 (i + 1 ) (rolling_max_f (INT_MIN) ((sublist (0) ((i + 1 )) (lv)))) )
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
.

Definition p009_rolling_max_return_wit_1 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
|--
  EX (output_l: (@list Z)) ,
  “ (out0 = out0) ” 
  &&  “ (problem_9_pre ) ” 
  &&  “ (problem_9_spec lv output_l ) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.full out0 out_size0 output_l )
.

Definition p009_rolling_max_partial_solve_wit_1 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
|--
  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (((numbers0 + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers0 i 0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
.

Definition p009_rolling_max_partial_solve_wit_2 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
|--
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (((numbers0 + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers0 i 0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
.

Definition p009_rolling_max_partial_solve_wit_3 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) <= max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
|--
  “ ((Znth i lv 0) <= max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (((out0 + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
.

Definition p009_rolling_max_partial_solve_wit_4 := 
forall (out_size0: Z) (out0: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (max: Z) (i: Z) ,
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
  **  (IntArray.undef_seg out0 i out_size0 )
|--
  “ ((Znth i lv 0) > max) ” 
  &&  “ (i < numbers_size0) ” 
  &&  “ (out_size0 = numbers_size0) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (max = (running_max_val (INT_MIN) ((sublist (0) (i) (lv))))) ”
  &&  (((out0 + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out0 (i + 1 ) out_size0 )
  **  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.seg out0 0 i (rolling_max_f (INT_MIN) ((sublist (0) (i) (lv)))) )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p009_rolling_max_safety_wit_1 : p009_rolling_max_safety_wit_1.
Axiom proof_of_p009_rolling_max_safety_wit_2 : p009_rolling_max_safety_wit_2.
Axiom proof_of_p009_rolling_max_safety_wit_3 : p009_rolling_max_safety_wit_3.
Axiom proof_of_p009_rolling_max_safety_wit_4 : p009_rolling_max_safety_wit_4.
Axiom proof_of_p009_rolling_max_safety_wit_5 : p009_rolling_max_safety_wit_5.
Axiom proof_of_p009_rolling_max_entail_wit_1 : p009_rolling_max_entail_wit_1.
Axiom proof_of_p009_rolling_max_entail_wit_2_1 : p009_rolling_max_entail_wit_2_1.
Axiom proof_of_p009_rolling_max_entail_wit_2_2 : p009_rolling_max_entail_wit_2_2.
Axiom proof_of_p009_rolling_max_return_wit_1 : p009_rolling_max_return_wit_1.
Axiom proof_of_p009_rolling_max_partial_solve_wit_1 : p009_rolling_max_partial_solve_wit_1.
Axiom proof_of_p009_rolling_max_partial_solve_wit_2 : p009_rolling_max_partial_solve_wit_2.
Axiom proof_of_p009_rolling_max_partial_solve_wit_3 : p009_rolling_max_partial_solve_wit_3.
Axiom proof_of_p009_rolling_max_partial_solve_wit_4 : p009_rolling_max_partial_solve_wit_4.

End VC_Correct.
