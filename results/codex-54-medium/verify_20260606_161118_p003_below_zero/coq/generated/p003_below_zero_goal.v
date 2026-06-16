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
Require Import p003_below_zero.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p003_below_zero -----*)

Definition p003_below_zero_safety_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  ((( &( "num" ) )) # Int  |->_)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p003_below_zero_safety_wit_2 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "num" ) )) # Int  |-> 0)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p003_below_zero_safety_wit_3 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
|--
  “ ((num + (Znth i l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num + (Znth i l 0) )) ”
.

Definition p003_below_zero_safety_wit_4 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  ((( &( "num" ) )) # Int  |-> (num + (Znth i l 0) ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p003_below_zero_safety_wit_5 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (i: Z) (num: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ (num < 0) ” 
  &&  “ (num = (sum ((sublist (0) ((i + 1 )) (l))))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p003_below_zero_safety_wit_6 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ ((num + (Znth i l 0) ) >= 0) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  ((( &( "num" ) )) # Int  |-> (num + (Znth i l 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p003_below_zero_safety_wit_7 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (i: Z) (num: Z) ,
  “ (i = operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "operations_size" ) )) # Int  |-> operations_size_pre)
  **  ((( &( "num" ) )) # Int  |-> num)
  **  ((( &( "operations" ) )) # Ptr  |-> operations_pre)
  **  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p003_below_zero_entail_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) ,
  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (0 = (sum ((sublist (0) (0) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
.

Definition p003_below_zero_entail_wit_2 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ ((num + (Znth i l 0) ) < 0) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= i) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ ((num + (Znth i l 0) ) < 0) ” 
  &&  “ ((num + (Znth i l 0) ) = (sum ((sublist (0) ((i + 1 )) (l))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
.

Definition p003_below_zero_entail_wit_3 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ ((num + (Znth i l 0) ) >= 0) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= operations_size_pre) ” 
  &&  “ ((num + (Znth i l 0) ) = (sum ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
.

Definition p003_below_zero_entail_wit_4 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ (i >= operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> (0 <= (sum ((sublist (0) ((k_3 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k_2 + 1 )) (l))))) /\ ((sum ((sublist (0) ((k_2 + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (i = operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
.

Definition p003_below_zero_return_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (i: Z) (num: Z) ,
  “ (i = operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k_3 + 1 )) (l)))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  (“ (0 = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l ))
  ||
  (EX (k_2: Z) ,
  “ (0 <> 0) ” 
  &&  “ (0 <= k_2) ” 
  &&  “ (k_2 < operations_size_pre) ” 
  &&  “ ((sum ((sublist (0) ((k_2 + 1 )) (l)))) < 0) ”
  &&  (IntArray.full operations_pre operations_size_pre l ))
.

Definition p003_below_zero_return_wit_2 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (i: Z) (num: Z) ,
  “ (0 <= i) ” 
  &&  “ (i < operations_size_pre) ” 
  &&  “ (num < 0) ” 
  &&  “ (num = (sum ((sublist (0) ((i + 1 )) (l))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  (“ (1 = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> (0 <= (sum ((sublist (0) ((k + 1 )) (l)))))) ”
  &&  (IntArray.full operations_pre operations_size_pre l ))
  ||
  (EX (k_2: Z) ,
  “ (1 <> 0) ” 
  &&  “ (0 <= k_2) ” 
  &&  “ (k_2 < operations_size_pre) ” 
  &&  “ ((sum ((sublist (0) ((k_2 + 1 )) (l)))) < 0) ”
  &&  (IntArray.full operations_pre operations_size_pre l ))
.

Definition p003_below_zero_partial_solve_wit_1 := 
forall (operations_size_pre: Z) (operations_pre: Z) (l: (@list Z)) (num: Z) (i: Z) ,
  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (IntArray.full operations_pre operations_size_pre l )
|--
  “ (i < operations_size_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= operations_size_pre) ” 
  &&  “ (num = (sum ((sublist (0) (i) (l))))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> (0 <= (sum ((sublist (0) ((k_2 + 1 )) (l)))))) ” 
  &&  “ (0 <= operations_size_pre) ” 
  &&  “ (operations_size_pre < INT_MAX) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < operations_size_pre)) -> ((INT_MIN <= (sum ((sublist (0) ((k + 1 )) (l))))) /\ ((sum ((sublist (0) ((k + 1 )) (l)))) <= INT_MAX))) ”
  &&  (((operations_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i operations_pre i 0 operations_size_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p003_below_zero_safety_wit_1 : p003_below_zero_safety_wit_1.
Axiom proof_of_p003_below_zero_safety_wit_2 : p003_below_zero_safety_wit_2.
Axiom proof_of_p003_below_zero_safety_wit_3 : p003_below_zero_safety_wit_3.
Axiom proof_of_p003_below_zero_safety_wit_4 : p003_below_zero_safety_wit_4.
Axiom proof_of_p003_below_zero_safety_wit_5 : p003_below_zero_safety_wit_5.
Axiom proof_of_p003_below_zero_safety_wit_6 : p003_below_zero_safety_wit_6.
Axiom proof_of_p003_below_zero_safety_wit_7 : p003_below_zero_safety_wit_7.
Axiom proof_of_p003_below_zero_entail_wit_1 : p003_below_zero_entail_wit_1.
Axiom proof_of_p003_below_zero_entail_wit_2 : p003_below_zero_entail_wit_2.
Axiom proof_of_p003_below_zero_entail_wit_3 : p003_below_zero_entail_wit_3.
Axiom proof_of_p003_below_zero_entail_wit_4 : p003_below_zero_entail_wit_4.
Axiom proof_of_p003_below_zero_return_wit_1 : p003_below_zero_return_wit_1.
Axiom proof_of_p003_below_zero_return_wit_2 : p003_below_zero_return_wit_2.
Axiom proof_of_p003_below_zero_partial_solve_wit_1 : p003_below_zero_partial_solve_wit_1.

End VC_Correct.
