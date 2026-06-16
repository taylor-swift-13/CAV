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
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p005_intersperse -----*)

Definition p005_intersperse_safety_wit_1 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p005_intersperse_safety_wit_2 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p005_intersperse_safety_wit_3 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre = 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ False ”
.

Definition p005_intersperse_safety_wit_4 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p005_intersperse_safety_wit_5 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ ((0 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 + 1 )) ”
.

Definition p005_intersperse_safety_wit_6 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p005_intersperse_safety_wit_7 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "k" ) )) # Int  |-> (0 + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p005_intersperse_safety_wit_8 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl: (@list Z)) (k: Z) (i: Z) ,
  “ (i < numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 (((2 * i ) - 1 ) + 1 ) (app (outl) ((cons (delimeter_pre) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition p005_intersperse_safety_wit_9 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl: (@list Z)) (k: Z) (i: Z) ,
  “ (i < numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 (((2 * i ) - 1 ) + 1 ) (app (outl) ((cons (delimeter_pre) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p005_intersperse_safety_wit_10 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (outl2) ((cons ((Znth i l 0)) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition p005_intersperse_safety_wit_11 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (outl2) ((cons ((Znth i l 0)) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p005_intersperse_safety_wit_12 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (outl2) ((cons ((Znth i l 0)) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out_pre)
  **  ((( &( "numbers" ) )) # Ptr  |-> numbers_pre)
  **  ((( &( "numbers_size" ) )) # Int  |-> numbers_size_pre)
  **  ((( &( "delimeter" ) )) # Int  |-> delimeter_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p005_intersperse_entail_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.undef_seg out_pre 1 ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  EX (outl: (@list Z)) ,
  “ (1 <= 1) ” 
  &&  “ (1 <= numbers_size_pre) ” 
  &&  “ ((0 + 1 ) = ((2 * 1 ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 ((2 * 1 ) - 1 ) outl )
  **  (IntArray.undef_seg out_pre ((2 * 1 ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
.

Definition p005_intersperse_entail_wit_2 := 
forall (out_pre: Z) (delimeter_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl: (@list Z)) (k: Z) (i: Z) ,
  “ (i < numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 (((2 * i ) - 1 ) + 1 ) (app (outl) ((cons (delimeter_pre) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  EX (outl2: (@list Z)) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ ((k + 1 ) = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (2 * i ) outl2 )
  **  (IntArray.undef_seg out_pre (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
.

Definition p005_intersperse_entail_wit_3 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.seg out_pre 0 ((2 * i ) + 1 ) (app (outl2) ((cons ((Znth i l 0)) (nil)))) )
  **  (IntArray.undef_missing_i out_pre k (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
|--
  EX (outl: (@list Z)) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= numbers_size_pre) ” 
  &&  “ ((k + 1 ) = ((2 * (i + 1 ) ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 ((2 * (i + 1 ) ) - 1 ) outl )
  **  (IntArray.undef_seg out_pre ((2 * (i + 1 ) ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
.

Definition p005_intersperse_return_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl_2: (@list Z)) (k: Z) (i: Z) ,
  “ (i >= numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 ((2 * i ) - 1 ) outl_2 )
  **  (IntArray.undef_seg out_pre ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
|--
  EX (outl: (@list Z)) ,
  “ ((Zlength (outl)) = ((2 * numbers_size_pre ) - 1 )) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.full out_pre ((2 * numbers_size_pre ) - 1 ) outl )
.

Definition p005_intersperse_partial_solve_wit_1 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((numbers_pre + (0 * sizeof(INT) ) )) # Int  |-> (Znth 0 l 0))
  **  (IntArray.missing_i numbers_pre 0 0 numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
.

Definition p005_intersperse_partial_solve_wit_2 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) ,
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.undef_full out_pre ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (numbers_size_pre <> 0) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg out_pre 1 ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
.

Definition p005_intersperse_partial_solve_wit_3 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl: (@list Z)) (k: Z) (i: Z) ,
  “ (i < numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 ((2 * i ) - 1 ) outl )
  **  (IntArray.undef_seg out_pre ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (i < numbers_size_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= numbers_size_pre) ” 
  &&  “ (k = ((2 * i ) - 1 )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre k ((2 * i ) - 1 ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 ((2 * i ) - 1 ) outl )
.

Definition p005_intersperse_partial_solve_wit_4 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (2 * i ) outl2 )
  **  (IntArray.undef_seg out_pre (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((numbers_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i numbers_pre i 0 numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (2 * i ) outl2 )
  **  (IntArray.undef_seg out_pre (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
.

Definition p005_intersperse_partial_solve_wit_5 := 
forall (out_pre: Z) (numbers_size_pre: Z) (numbers_pre: Z) (l: (@list Z)) (outl2: (@list Z)) (i: Z) (k: Z) ,
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (2 * i ) outl2 )
  **  (IntArray.undef_seg out_pre (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
|--
  “ (1 <= i) ” 
  &&  “ (i < numbers_size_pre) ” 
  &&  “ (k = (2 * i )) ” 
  &&  “ (0 < numbers_size_pre) ” 
  &&  “ (((2 * numbers_size_pre ) - 1 ) < INT_MAX) ” 
  &&  “ ((Zlength (l)) = numbers_size_pre) ”
  &&  (((out_pre + (k * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_missing_i out_pre k (2 * i ) ((2 * numbers_size_pre ) - 1 ) )
  **  (IntArray.full numbers_pre numbers_size_pre l )
  **  (IntArray.seg out_pre 0 (2 * i ) outl2 )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p005_intersperse_safety_wit_1 : p005_intersperse_safety_wit_1.
Axiom proof_of_p005_intersperse_safety_wit_2 : p005_intersperse_safety_wit_2.
Axiom proof_of_p005_intersperse_safety_wit_3 : p005_intersperse_safety_wit_3.
Axiom proof_of_p005_intersperse_safety_wit_4 : p005_intersperse_safety_wit_4.
Axiom proof_of_p005_intersperse_safety_wit_5 : p005_intersperse_safety_wit_5.
Axiom proof_of_p005_intersperse_safety_wit_6 : p005_intersperse_safety_wit_6.
Axiom proof_of_p005_intersperse_safety_wit_7 : p005_intersperse_safety_wit_7.
Axiom proof_of_p005_intersperse_safety_wit_8 : p005_intersperse_safety_wit_8.
Axiom proof_of_p005_intersperse_safety_wit_9 : p005_intersperse_safety_wit_9.
Axiom proof_of_p005_intersperse_safety_wit_10 : p005_intersperse_safety_wit_10.
Axiom proof_of_p005_intersperse_safety_wit_11 : p005_intersperse_safety_wit_11.
Axiom proof_of_p005_intersperse_safety_wit_12 : p005_intersperse_safety_wit_12.
Axiom proof_of_p005_intersperse_entail_wit_1 : p005_intersperse_entail_wit_1.
Axiom proof_of_p005_intersperse_entail_wit_2 : p005_intersperse_entail_wit_2.
Axiom proof_of_p005_intersperse_entail_wit_3 : p005_intersperse_entail_wit_3.
Axiom proof_of_p005_intersperse_return_wit_1 : p005_intersperse_return_wit_1.
Axiom proof_of_p005_intersperse_partial_solve_wit_1 : p005_intersperse_partial_solve_wit_1.
Axiom proof_of_p005_intersperse_partial_solve_wit_2 : p005_intersperse_partial_solve_wit_2.
Axiom proof_of_p005_intersperse_partial_solve_wit_3 : p005_intersperse_partial_solve_wit_3.
Axiom proof_of_p005_intersperse_partial_solve_wit_4 : p005_intersperse_partial_solve_wit_4.
Axiom proof_of_p005_intersperse_partial_solve_wit_5 : p005_intersperse_partial_solve_wit_5.

End VC_Correct.
