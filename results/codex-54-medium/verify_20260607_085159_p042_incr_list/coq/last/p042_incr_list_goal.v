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
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

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
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) (data_v_2: Z) (out_v_2: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (input_l) (0)))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((( &( "out" ) )) # Ptr  |-> out_v_2)
  **  ((( &( "data" ) )) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_v_2 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v_2 i l_size_pre )
|--
  “ (((Znth (i) (input_l) (0)) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth (i) (input_l) (0)) + 1 )) ”
.

Definition p042_incr_list_safety_wit_3 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) (data_v_2: Z) (out_v_2: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (input_l) (0)))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((( &( "out" ) )) # Ptr  |-> out_v_2)
  **  ((( &( "data" ) )) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_v_2 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v_2 i l_size_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p042_incr_list_safety_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) (data_v_2: Z) (out_v_2: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  (IntArray.seg data_v_2 0 (i + 1 ) (app ((map_incr ((sublist (0) (i) (input_l))))) ((cons (((Znth (i) (input_l) (0)) + 1 )) (nil)))) )
  **  (IntArray.full l_pre l_size_pre (replace_Znth (i) ((Znth (i) (input_l) (0))) (input_l)) )
  **  (IntArray.undef_seg data_v_2 (i + 1 ) l_size_pre )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_v_2)
  **  ((( &( "data" ) )) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
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
  “ (0 <= 0) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg retval_2 0 0 (map_incr ((sublist (0) (0) (input_l)))) )
  **  (IntArray.undef_seg retval_2 0 l_size_pre )
.

Definition p042_incr_list_entail_wit_2 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v_2: Z) (out_v_2: Z) (i: Z) (data_v: Z) (out_v: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  (IntArray.seg data_v 0 (i + 1 ) (app ((map_incr ((sublist (0) (i) (input_l))))) ((cons (((Znth (i) (input_l) (0)) + 1 )) (nil)))) )
  **  (IntArray.full l_pre l_size_pre (replace_Znth (i) ((Znth (i) (input_l) (0))) (input_l)) )
  **  (IntArray.undef_seg data_v (i + 1 ) l_size_pre )
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 (i + 1 ) (map_incr ((sublist (0) ((i + 1 )) (input_l)))) )
  **  (IntArray.undef_seg data_v (i + 1 ) l_size_pre )
.

Definition p042_incr_list_return_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) ,
  “ (i >= l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out_v <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = l_size_pre) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (output_l = (map_incr (input_l))) ” 
  &&  “ (problem_42_spec input_l output_l ) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
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

Definition p042_incr_list_partial_solve_wit_3_pure := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "l" ) )) # Ptr  |-> l_pre)
  **  ((( &( "l_size" ) )) # Int  |-> l_size_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out_v)
  **  ((( &( "data" ) )) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
|--
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
.

Definition p042_incr_list_partial_solve_wit_3_aux := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) ,
  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
|--
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
.

Definition p042_incr_list_partial_solve_wit_3 := p042_incr_list_partial_solve_wit_3_pure -> p042_incr_list_partial_solve_wit_3_aux.

Definition p042_incr_list_partial_solve_wit_4 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) (data_v_2: Z) (out_v_2: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (input_l) (0)))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_v_2 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v_2 i l_size_pre )
|--
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v_2 <> 0) ” 
  &&  “ (data_v_2 <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  (((data_v_2 + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data_v_2 (i + 1 ) l_size_pre )
  **  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (input_l) (0)))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v_2)
  **  ((&((out_v_2)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_v_2 0 i (map_incr ((sublist (0) (i) (input_l)))) )
.

Definition p042_incr_list_which_implies_wit_1 := 
forall (l_size_pre: Z) (l_pre: Z) (input_l: (@list Z)) (data_v: Z) (out_v: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.full l_pre l_size_pre input_l )
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
|--
  “ (0 <= i) ” 
  &&  “ (i < l_size_pre) ” 
  &&  “ (out_v <> 0) ” 
  &&  “ (data_v <> 0) ” 
  &&  “ (l_size_pre = (Zlength (input_l))) ” 
  &&  “ (list_incr_int_range input_l ) ” 
  &&  “ (0 <= l_size_pre) ” 
  &&  “ (l_size_pre < INT_MAX) ”
  &&  (((l_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth (i) (input_l) (0)))
  **  (IntArray.missing_i l_pre i 0 l_size_pre input_l )
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_v)
  **  ((&((out_v)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> l_size_pre)
  **  (IntArray.seg data_v 0 i (map_incr ((sublist (0) (i) (input_l)))) )
  **  (IntArray.undef_seg data_v i l_size_pre )
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
Axiom proof_of_p042_incr_list_partial_solve_wit_3_pure : p042_incr_list_partial_solve_wit_3_pure.
Axiom proof_of_p042_incr_list_partial_solve_wit_3 : p042_incr_list_partial_solve_wit_3.
Axiom proof_of_p042_incr_list_partial_solve_wit_4 : p042_incr_list_partial_solve_wit_4.
Axiom proof_of_p042_incr_list_which_implies_wit_1 : p042_incr_list_which_implies_wit_1.

End VC_Correct.
