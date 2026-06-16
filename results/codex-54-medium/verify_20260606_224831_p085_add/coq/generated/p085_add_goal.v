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
Require Import p085_add.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function p085_add -----*)

Definition p085_add_safety_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "s" ) )) # Int  |->_)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p085_add_safety_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Int  |-> 0)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p085_add_safety_wit_3 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition p085_add_safety_wit_4 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition p085_add_safety_wit_5 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p085_add_safety_wit_6 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p085_add_safety_wit_7 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (((Znth ((i * 2 ) + 1 ) lv 0) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p085_add_safety_wit_8 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition p085_add_safety_wit_9 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition p085_add_safety_wit_10 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p085_add_safety_wit_11 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
  **  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p085_add_safety_wit_12 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p085_add_safety_wit_13 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p085_add_safety_wit_14 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ ((s + (Znth ((i * 2 ) + 1 ) lv 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (s + (Znth ((i * 2 ) + 1 ) lv 0) )) ”
.

Definition p085_add_safety_wit_15 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (((i * 2 ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((i * 2 ) + 1 )) ”
.

Definition p085_add_safety_wit_16 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ ((i * 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * 2 )) ”
.

Definition p085_add_safety_wit_17 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p085_add_safety_wit_18 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p085_add_safety_wit_19 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) <> 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> s)
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p085_add_safety_wit_20 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "lst_size" ) )) # Int  |-> lst_size_pre)
  **  ((( &( "s" ) )) # Int  |-> (s + (Znth ((i * 2 ) + 1 ) lv 0) ))
  **  ((( &( "lst" ) )) # Ptr  |-> lst_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p085_add_entail_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) ,
  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (0 <= 0) ” 
  &&  “ ((2 * 0 ) <= lst_size_pre) ” 
  &&  “ (0 = (sum_even_at_odd_upto (0) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition p085_add_entail_wit_2_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= lst_size_pre) ” 
  &&  “ ((s + (Znth ((i * 2 ) + 1 ) lv 0) ) = (sum_even_at_odd_upto ((i + 1 )) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition p085_add_entail_wit_2_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) <> 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((2 * (i + 1 ) ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto ((i + 1 )) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition p085_add_return_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) >= lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (problem_85_spec lv s ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
.

Definition p085_add_partial_solve_wit_1 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (((lst_pre + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) lv 0))
  **  (IntArray.missing_i lst_pre ((i * 2 ) + 1 ) 0 lst_size_pre lv )
.

Definition p085_add_partial_solve_wit_2 := 
forall (lst_size_pre: Z) (lst_pre: Z) (lv: (@list Z)) (s: Z) (i: Z) ,
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (IntArray.full lst_pre lst_size_pre lv )
|--
  “ (((Znth ((i * 2 ) + 1 ) lv 0) % ( 2 ) ) = 0) ” 
  &&  “ (((i * 2 ) + 1 ) < lst_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ ((2 * i ) <= lst_size_pre) ” 
  &&  “ (s = (sum_even_at_odd_upto (i) (lv))) ” 
  &&  “ (0 <= lst_size_pre) ” 
  &&  “ (lst_size_pre < INT_MAX) ” 
  &&  “ (lst_size_pre = (Zlength (lv))) ” 
  &&  “ (problem_85_pre lv ) ” 
  &&  “ (add_int_range lv ) ”
  &&  (((lst_pre + (((i * 2 ) + 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i * 2 ) + 1 ) lv 0))
  **  (IntArray.missing_i lst_pre ((i * 2 ) + 1 ) 0 lst_size_pre lv )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p085_add_safety_wit_1 : p085_add_safety_wit_1.
Axiom proof_of_p085_add_safety_wit_2 : p085_add_safety_wit_2.
Axiom proof_of_p085_add_safety_wit_3 : p085_add_safety_wit_3.
Axiom proof_of_p085_add_safety_wit_4 : p085_add_safety_wit_4.
Axiom proof_of_p085_add_safety_wit_5 : p085_add_safety_wit_5.
Axiom proof_of_p085_add_safety_wit_6 : p085_add_safety_wit_6.
Axiom proof_of_p085_add_safety_wit_7 : p085_add_safety_wit_7.
Axiom proof_of_p085_add_safety_wit_8 : p085_add_safety_wit_8.
Axiom proof_of_p085_add_safety_wit_9 : p085_add_safety_wit_9.
Axiom proof_of_p085_add_safety_wit_10 : p085_add_safety_wit_10.
Axiom proof_of_p085_add_safety_wit_11 : p085_add_safety_wit_11.
Axiom proof_of_p085_add_safety_wit_12 : p085_add_safety_wit_12.
Axiom proof_of_p085_add_safety_wit_13 : p085_add_safety_wit_13.
Axiom proof_of_p085_add_safety_wit_14 : p085_add_safety_wit_14.
Axiom proof_of_p085_add_safety_wit_15 : p085_add_safety_wit_15.
Axiom proof_of_p085_add_safety_wit_16 : p085_add_safety_wit_16.
Axiom proof_of_p085_add_safety_wit_17 : p085_add_safety_wit_17.
Axiom proof_of_p085_add_safety_wit_18 : p085_add_safety_wit_18.
Axiom proof_of_p085_add_safety_wit_19 : p085_add_safety_wit_19.
Axiom proof_of_p085_add_safety_wit_20 : p085_add_safety_wit_20.
Axiom proof_of_p085_add_entail_wit_1 : p085_add_entail_wit_1.
Axiom proof_of_p085_add_entail_wit_2_1 : p085_add_entail_wit_2_1.
Axiom proof_of_p085_add_entail_wit_2_2 : p085_add_entail_wit_2_2.
Axiom proof_of_p085_add_return_wit_1 : p085_add_return_wit_1.
Axiom proof_of_p085_add_partial_solve_wit_1 : p085_add_partial_solve_wit_1.
Axiom proof_of_p085_add_partial_solve_wit_2 : p085_add_partial_solve_wit_2.

End VC_Correct.
