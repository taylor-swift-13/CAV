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

(*----- Function array_fill_value -----*)

Definition array_fill_value_safety_wit_1 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full a_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition array_fill_value_safety_wit_2 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j lr 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((i <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) (k_pre) (lr)) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "k" ) )) # Int  |-> k_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition array_fill_value_entail_wit_1 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre l )
|--
  EX (lr: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Znth j lr 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_fill_value_entail_wit_2 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (lr_2)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j lr_2 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((i <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr_2 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre (replace_Znth (i) (k_pre) (lr_2)) )
|--
  EX (lr: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Znth j lr 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , ((((i + 1 ) <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_fill_value_return_wit_1 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (lr_2: (@list Z)) (i_2: Z) ,
  “ (i_2 >= n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ ((Zlength (lr_2)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i_2)) -> ((Znth j lr_2 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((i_2 <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr_2 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre lr_2 )
|--
  EX (lr: (@list Z)) ,
  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < n_pre)) -> ((Znth i lr 0) = k_pre)) ”
  &&  (IntArray.full a_pre n_pre lr )
.

Definition array_fill_value_partial_solve_wit_1 := 
forall (a_pre: Z) (k_pre: Z) (n_pre: Z) (l: (@list Z)) (lr: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j lr 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((i <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full a_pre n_pre lr )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ ((Zlength (lr)) = n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Znth j lr 0) = k_pre)) ” 
  &&  “ forall (j_2: Z) , (((i <= j_2) /\ (j_2 < n_pre)) -> ((Znth j_2 lr 0) = (Znth j_2 l 0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((a_pre + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i a_pre i 0 n_pre lr )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_array_fill_value_safety_wit_1 : array_fill_value_safety_wit_1.
Axiom proof_of_array_fill_value_safety_wit_2 : array_fill_value_safety_wit_2.
Axiom proof_of_array_fill_value_entail_wit_1 : array_fill_value_entail_wit_1.
Axiom proof_of_array_fill_value_entail_wit_2 : array_fill_value_entail_wit_2.
Axiom proof_of_array_fill_value_return_wit_1 : array_fill_value_return_wit_1.
Axiom proof_of_array_fill_value_partial_solve_wit_1 : array_fill_value_partial_solve_wit_1.

End VC_Correct.
