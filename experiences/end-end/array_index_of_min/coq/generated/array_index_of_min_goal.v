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
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function array_index_of_min -----*)

Definition array_index_of_min_safety_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_index_of_min_safety_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "idx" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition array_index_of_min_safety_wit_3 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ ((Znth i l 0) >= (Znth idx l 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_index_of_min_safety_wit_4 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ ((Znth i l 0) < (Znth idx l 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "idx" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_index_of_min_entail_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < 1) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 1)) -> ((Znth 0 l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < 0)) -> ((Znth j_2 l 0) > (Znth 0 l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_index_of_min_entail_wit_2_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ ((Znth i l 0) < (Znth idx l 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth i l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < i)) -> ((Znth j_2 l 0) > (Znth i l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_index_of_min_entail_wit_2_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ ((Znth i l 0) >= (Znth idx l 0)) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < (i + 1 )) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_index_of_min_return_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j_3: Z) , (((0 <= j_3) /\ (j_3 < i)) -> ((Znth idx l 0) <= (Znth j_3 l 0))) ” 
  &&  “ forall (j_4: Z) , (((0 <= j_4) /\ (j_4 < idx)) -> ((Znth j_4 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= idx) ” 
  &&  “ (idx < n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < n_pre)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ”
  &&  (IntArray.full a_pre n_pre l )
.

Definition array_index_of_min_partial_solve_wit_1 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i a_pre i 0 n_pre l )
.

Definition array_index_of_min_partial_solve_wit_2 := 
forall (a_pre: Z) (n_pre: Z) (l: (@list Z)) (idx: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < i) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth idx l 0) <= (Znth j l 0))) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < idx)) -> ((Znth j_2 l 0) > (Znth idx l 0))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((a_pre + (idx * sizeof(INT) ) )) # Int  |-> (Znth idx l 0))
  **  (IntArray.missing_i a_pre idx 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_index_of_min_safety_wit_1 : array_index_of_min_safety_wit_1.
Axiom proof_of_array_index_of_min_safety_wit_2 : array_index_of_min_safety_wit_2.
Axiom proof_of_array_index_of_min_safety_wit_3 : array_index_of_min_safety_wit_3.
Axiom proof_of_array_index_of_min_safety_wit_4 : array_index_of_min_safety_wit_4.
Axiom proof_of_array_index_of_min_entail_wit_1 : array_index_of_min_entail_wit_1.
Axiom proof_of_array_index_of_min_entail_wit_2_1 : array_index_of_min_entail_wit_2_1.
Axiom proof_of_array_index_of_min_entail_wit_2_2 : array_index_of_min_entail_wit_2_2.
Axiom proof_of_array_index_of_min_return_wit_1 : array_index_of_min_return_wit_1.
Axiom proof_of_array_index_of_min_partial_solve_wit_1 : array_index_of_min_partial_solve_wit_1.
Axiom proof_of_array_index_of_min_partial_solve_wit_2 : array_index_of_min_partial_solve_wit_2.

End VC_Correct.
