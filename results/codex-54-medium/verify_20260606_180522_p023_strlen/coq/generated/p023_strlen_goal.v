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
Require Import p023_strlen.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p023_strlen -----*)

Definition p023_strlen_safety_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p023_strlen_safety_wit_2 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p023_strlen_safety_wit_3 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p023_strlen_safety_wit_4 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p023_strlen_entail_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p023_strlen_entail_wit_2 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p023_strlen_return_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (i = n) ” 
  &&  “ (problem_23_spec l i ) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p023_strlen_partial_solve_wit_1 := 
forall (str_pre: Z) (n: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_23_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p023_strlen_safety_wit_1 : p023_strlen_safety_wit_1.
Axiom proof_of_p023_strlen_safety_wit_2 : p023_strlen_safety_wit_2.
Axiom proof_of_p023_strlen_safety_wit_3 : p023_strlen_safety_wit_3.
Axiom proof_of_p023_strlen_safety_wit_4 : p023_strlen_safety_wit_4.
Axiom proof_of_p023_strlen_entail_wit_1 : p023_strlen_entail_wit_1.
Axiom proof_of_p023_strlen_entail_wit_2 : p023_strlen_entail_wit_2.
Axiom proof_of_p023_strlen_return_wit_1 : p023_strlen_return_wit_1.
Axiom proof_of_p023_strlen_partial_solve_wit_1 : p023_strlen_partial_solve_wit_1.

End VC_Correct.
