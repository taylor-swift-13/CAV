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
Require Import array_count_odd.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_count_odd -----*)

Definition array_count_odd_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_count_odd_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_count_odd_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (((Znth i l 0) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition array_count_odd_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition array_count_odd_safety_wit_5 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_count_odd_safety_wit_6 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (((Znth i l 0) % ( 2 ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition array_count_odd_safety_wit_7 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (((Znth i l 0) % ( 2 ) ) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_count_odd_safety_wit_8 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (((Znth i l 0) % ( 2 ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_count_odd_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (IntArray.full a_pre n_pre l )
.

Definition array_count_odd_entail_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (n_pre <= INT_MAX) ” 
  &&  “ (0 <= INT_MAX) ” 
  &&  “ (0 >= INT_MIN) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (array_count_odd_spec ((sublist (0) (0) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_odd_entail_wit_3_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (((Znth i l 0) % ( 2 ) ) <> 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (array_count_odd_spec ((sublist (0) ((i + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_odd_entail_wit_3_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (((Znth i l 0) % ( 2 ) ) = 0) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) ((i + 1 )) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_odd_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (count = (array_count_odd_spec (l))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_count_odd_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (array_count_odd_spec ((sublist (0) (i) (l))))) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_count_odd_safety_wit_1 : array_count_odd_safety_wit_1.
Axiom proof_of_array_count_odd_safety_wit_2 : array_count_odd_safety_wit_2.
Axiom proof_of_array_count_odd_safety_wit_3 : array_count_odd_safety_wit_3.
Axiom proof_of_array_count_odd_safety_wit_4 : array_count_odd_safety_wit_4.
Axiom proof_of_array_count_odd_safety_wit_5 : array_count_odd_safety_wit_5.
Axiom proof_of_array_count_odd_safety_wit_6 : array_count_odd_safety_wit_6.
Axiom proof_of_array_count_odd_safety_wit_7 : array_count_odd_safety_wit_7.
Axiom proof_of_array_count_odd_safety_wit_8 : array_count_odd_safety_wit_8.
Axiom proof_of_array_count_odd_entail_wit_1 : array_count_odd_entail_wit_1.
Axiom proof_of_array_count_odd_entail_wit_2 : array_count_odd_entail_wit_2.
Axiom proof_of_array_count_odd_entail_wit_3_1 : array_count_odd_entail_wit_3_1.
Axiom proof_of_array_count_odd_entail_wit_3_2 : array_count_odd_entail_wit_3_2.
Axiom proof_of_array_count_odd_return_wit_1 : array_count_odd_return_wit_1.
Axiom proof_of_array_count_odd_partial_solve_wit_1 : array_count_odd_partial_solve_wit_1.

End VC_Correct.
