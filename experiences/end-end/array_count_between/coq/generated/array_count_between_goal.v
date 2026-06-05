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
Require Import array_count_between.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_count_between -----*)

Definition array_count_between_safety_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_count_between_safety_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_count_between_safety_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) <= hi_pre) ” 
  &&  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition array_count_between_safety_wit_4 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) > hi_pre) ” 
  &&  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_count_between_safety_wit_5 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) < lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_count_between_safety_wit_6 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) <= hi_pre) ” 
  &&  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_count_between_entail_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "hi" ) )) # Int  |-> hi_pre)
  **  ((( &( "lo" ) )) # Int  |-> lo_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_entail_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 = (array_count_between_spec ((sublist (0) (0) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_entail_wit_3_1 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) <= hi_pre) ” 
  &&  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((count + 1 ) = (array_count_between_spec ((sublist (0) ((i + 1 )) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_entail_wit_3_2 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) < lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) ((i + 1 )) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_entail_wit_3_3 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) > hi_pre) ” 
  &&  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) ((i + 1 )) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_return_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (count = (array_count_between_spec (l) (lo_pre) (hi_pre))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_between_partial_solve_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_count_between_partial_solve_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ ((Znth i l 0) >= lo_pre) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (count = (array_count_between_spec ((sublist (0) (i) (l))) (lo_pre) (hi_pre))) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (lo_pre <= INT_MAX) ” 
  &&  “ (hi_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (lo_pre >= INT_MIN) ” 
  &&  “ (hi_pre >= INT_MIN) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (lo_pre <= hi_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_count_between_safety_wit_1 : array_count_between_safety_wit_1.
Axiom proof_of_array_count_between_safety_wit_2 : array_count_between_safety_wit_2.
Axiom proof_of_array_count_between_safety_wit_3 : array_count_between_safety_wit_3.
Axiom proof_of_array_count_between_safety_wit_4 : array_count_between_safety_wit_4.
Axiom proof_of_array_count_between_safety_wit_5 : array_count_between_safety_wit_5.
Axiom proof_of_array_count_between_safety_wit_6 : array_count_between_safety_wit_6.
Axiom proof_of_array_count_between_entail_wit_1 : array_count_between_entail_wit_1.
Axiom proof_of_array_count_between_entail_wit_2 : array_count_between_entail_wit_2.
Axiom proof_of_array_count_between_entail_wit_3_1 : array_count_between_entail_wit_3_1.
Axiom proof_of_array_count_between_entail_wit_3_2 : array_count_between_entail_wit_3_2.
Axiom proof_of_array_count_between_entail_wit_3_3 : array_count_between_entail_wit_3_3.
Axiom proof_of_array_count_between_return_wit_1 : array_count_between_return_wit_1.
Axiom proof_of_array_count_between_partial_solve_wit_1 : array_count_between_partial_solve_wit_1.
Axiom proof_of_array_count_between_partial_solve_wit_2 : array_count_between_partial_solve_wit_2.

End VC_Correct.
