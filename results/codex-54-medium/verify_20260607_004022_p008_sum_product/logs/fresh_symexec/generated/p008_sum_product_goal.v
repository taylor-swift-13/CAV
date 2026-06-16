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
Require Import p008_sum_product.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function p008_sum_product -----*)

Definition p008_sum_product_safety_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p008_sum_product_safety_wit_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p008_sum_product_safety_wit_3 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p008_sum_product_safety_wit_4 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p008_sum_product_safety_wit_5 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ ((sum + (Znth i lv 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i lv 0) )) ”
.

Definition p008_sum_product_safety_wit_6 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i lv 0) ))
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ ((product * (Znth i lv 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (product * (Znth i lv 0) )) ”
.

Definition p008_sum_product_safety_wit_7 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i lv 0) ))
  **  ((( &( "product" ) )) # Int  |-> (product * (Znth i lv 0) ))
  **  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p008_sum_product_safety_wit_8 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  (IntArray.undef_full retval 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p008_sum_product_safety_wit_9 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.undef_seg retval 1 2 )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "product" ) )) # Int  |-> product)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p008_sum_product_entail_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (0 = (prefix_sum (lv) (0))) ” 
  &&  “ (1 = (prefix_product (lv) (0))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "numbers_size" ) )) # Int  |-> numbers_size0)
  **  (IntArray.undef_full retval 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
.

Definition p008_sum_product_entail_wit_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full retval 2 )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numbers_size0) ” 
  &&  “ ((sum + (Znth i lv 0) ) = (prefix_sum (lv) ((i + 1 )))) ” 
  &&  “ ((product * (Znth i lv 0) ) = (prefix_product (lv) ((i + 1 )))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
.

Definition p008_sum_product_return_wit_1 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |-> product)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  EX (s: Z)  (p: Z) ,
  “ (retval <> 0) ” 
  &&  “ (problem_8_spec lv s p ) ”
  &&  (IntArray.full numbers0 numbers_size0 lv )
  **  (IntArray.full retval 2 (cons (s) ((cons (p) (nil)))) )
.

Definition p008_sum_product_partial_solve_wit_1_pure := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "product" ) )) # Int  |-> 1)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition p008_sum_product_partial_solve_wit_1_aux := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) ,
  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
.

Definition p008_sum_product_partial_solve_wit_1 := p008_sum_product_partial_solve_wit_1_pure -> p008_sum_product_partial_solve_wit_1_aux.

Definition p008_sum_product_partial_solve_wit_2 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((numbers_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers_pre i 0 numbers_size_pre lv )
  **  (IntArray.undef_full retval 2 )
.

Definition p008_sum_product_partial_solve_wit_3 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.full numbers_pre numbers_size_pre lv )
  **  (IntArray.undef_full retval 2 )
|--
  “ (i < numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((numbers_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i lv 0))
  **  (IntArray.missing_i numbers_pre i 0 numbers_size_pre lv )
  **  (IntArray.undef_full retval 2 )
.

Definition p008_sum_product_partial_solve_wit_4 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval 1 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
.

Definition p008_sum_product_partial_solve_wit_5 := 
forall (numbers_size_pre: Z) (numbers_pre: Z) (numbers_size0: Z) (numbers0: Z) (lv: (@list Z)) (retval: Z) (product: Z) (sum: Z) (i: Z) ,
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.undef_seg retval 1 2 )
  **  (IntArray.full numbers_pre numbers_size_pre lv )
|--
  “ (i >= numbers_size0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= numbers_size0) ” 
  &&  “ (sum = (prefix_sum (lv) (i))) ” 
  &&  “ (product = (prefix_product (lv) (i))) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (numbers_pre = numbers0) ” 
  &&  “ (numbers_size_pre = numbers_size0) ” 
  &&  “ (0 <= numbers_size0) ” 
  &&  “ (numbers_size0 < INT_MAX) ” 
  &&  “ (problem_8_pre ) ” 
  &&  “ (list_int_range lv ) ” 
  &&  “ (prefix_sum_product_int_range lv numbers_size0 ) ”
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> sum)
  **  (IntArray.full numbers_pre numbers_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p008_sum_product_safety_wit_1 : p008_sum_product_safety_wit_1.
Axiom proof_of_p008_sum_product_safety_wit_2 : p008_sum_product_safety_wit_2.
Axiom proof_of_p008_sum_product_safety_wit_3 : p008_sum_product_safety_wit_3.
Axiom proof_of_p008_sum_product_safety_wit_4 : p008_sum_product_safety_wit_4.
Axiom proof_of_p008_sum_product_safety_wit_5 : p008_sum_product_safety_wit_5.
Axiom proof_of_p008_sum_product_safety_wit_6 : p008_sum_product_safety_wit_6.
Axiom proof_of_p008_sum_product_safety_wit_7 : p008_sum_product_safety_wit_7.
Axiom proof_of_p008_sum_product_safety_wit_8 : p008_sum_product_safety_wit_8.
Axiom proof_of_p008_sum_product_safety_wit_9 : p008_sum_product_safety_wit_9.
Axiom proof_of_p008_sum_product_entail_wit_1 : p008_sum_product_entail_wit_1.
Axiom proof_of_p008_sum_product_entail_wit_2 : p008_sum_product_entail_wit_2.
Axiom proof_of_p008_sum_product_return_wit_1 : p008_sum_product_return_wit_1.
Axiom proof_of_p008_sum_product_partial_solve_wit_1_pure : p008_sum_product_partial_solve_wit_1_pure.
Axiom proof_of_p008_sum_product_partial_solve_wit_1 : p008_sum_product_partial_solve_wit_1.
Axiom proof_of_p008_sum_product_partial_solve_wit_2 : p008_sum_product_partial_solve_wit_2.
Axiom proof_of_p008_sum_product_partial_solve_wit_3 : p008_sum_product_partial_solve_wit_3.
Axiom proof_of_p008_sum_product_partial_solve_wit_4 : p008_sum_product_partial_solve_wit_4.
Axiom proof_of_p008_sum_product_partial_solve_wit_5 : p008_sum_product_partial_solve_wit_5.

End VC_Correct.
