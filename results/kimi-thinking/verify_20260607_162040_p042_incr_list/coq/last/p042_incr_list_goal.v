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
Require Import p042_incr_list.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p042_incr_list -----*)

Definition p042_incr_list_safety_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p042_incr_list_safety_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app (output_prefix) ((cons (((Znth i input_l 0) + 1 )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p042_incr_list_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
  **  (IntArray.undef_seg data i l_size_pre )
|--
  “ (((Znth i input_l 0) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i input_l 0) + 1 )) ”
.

Definition p042_incr_list_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
  **  (IntArray.undef_seg data i l_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p042_incr_list_entail_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.undef_full retval_2 l_size_pre )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  EX (output_prefix: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = 0) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (0) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  (IntArray.seg retval_2 0 0 output_prefix )
  **  (IntArray.undef_seg retval_2 0 l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition p042_incr_list_entail_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix_2: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix_2)) = i) ” 
  &&  “ (output_prefix_2 = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app (output_prefix_2) ((cons (((Znth i input_l 0) + 1 )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
|--
  EX (output_prefix: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = (i + 1 )) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) ((i + 1 )) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 (i + 1 ) output_prefix )
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition p042_incr_list_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data_2: Z) (out: Z) (i: Z) ,
  “ (i >= l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  (IntArray.seg data_2 0 i output_prefix )
  **  (IntArray.undef_seg data_2 i l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = l_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (output_l = (map_incr (input_l))) ” 
  &&  “ (problem_42_spec input_l output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.full data output_size output_l )
.

Definition p042_incr_list_partial_solve_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) ,
  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.full l_pre l_size_pre input_l )
|--
  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.full l_pre l_size_pre input_l )
.

Definition p042_incr_list_partial_solve_wit_2_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  “ (l_size_pre >= 0) ” 
  &&  “ (l_size_pre < INT_MAX) ”
.

Definition p042_incr_list_partial_solve_wit_2_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  “ (l_size_pre >= 0) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
.

Definition p042_incr_list_partial_solve_wit_2 := p042_incr_list_partial_solve_wit_2_pure -> p042_incr_list_partial_solve_wit_2_aux.

Definition p042_incr_list_partial_solve_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
  **  (IntArray.undef_seg data i l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
|--
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i input_l 0))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
  **  (IntArray.undef_seg data i l_size_pre )
.

Definition p042_incr_list_partial_solve_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (output_prefix: (@list Z)) (data: Z) (out: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
  **  (IntArray.undef_seg data i l_size_pre )
|--
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ ((Zlength (output_prefix)) = i) ” 
  &&  “ (output_prefix = (map_incr ((sublist (0) (i) (input_l))))) ” 
  &&  “ (problem_42_pre input_l ) ” 
  &&  “ (list_incr_int_range input_l ) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) l_size_pre )
  **  (IntArray.full l_pre l_size_pre input_l )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  (IntArray.seg data 0 i output_prefix )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p042_incr_list_safety_wit_1 : p042_incr_list_safety_wit_1.
Axiom proof_of_p042_incr_list_safety_wit_2 : p042_incr_list_safety_wit_2.
Axiom proof_of_p042_incr_list_safety_wit_3 : p042_incr_list_safety_wit_3.
Axiom proof_of_p042_incr_list_safety_wit_4 : p042_incr_list_safety_wit_4.
Axiom proof_of_p042_incr_list_entail_wit_1 : p042_incr_list_entail_wit_1.
Axiom proof_of_p042_incr_list_entail_wit_2 : p042_incr_list_entail_wit_2.
Axiom proof_of_p042_incr_list_return_wit_1 : p042_incr_list_return_wit_1.
Axiom proof_of_p042_incr_list_partial_solve_wit_1 : p042_incr_list_partial_solve_wit_1.
Axiom proof_of_p042_incr_list_partial_solve_wit_2_pure : p042_incr_list_partial_solve_wit_2_pure.
Axiom proof_of_p042_incr_list_partial_solve_wit_2 : p042_incr_list_partial_solve_wit_2.
Axiom proof_of_p042_incr_list_partial_solve_wit_3 : p042_incr_list_partial_solve_wit_3.
Axiom proof_of_p042_incr_list_partial_solve_wit_4 : p042_incr_list_partial_solve_wit_4.

End VC_Correct.
