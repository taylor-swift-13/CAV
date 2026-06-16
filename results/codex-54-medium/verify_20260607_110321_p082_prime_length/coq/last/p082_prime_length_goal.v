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
Require Import p082_prime_length.
Local Open Scope sac.
From SimpleC.EE.annotated Require Import char_array_strategy_goal.
From SimpleC.EE.annotated Require Import char_array_strategy_proof.

(*----- Function p082_prime_length -----*)

Definition p082_prime_length_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p082_prime_length_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 2) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p082_prime_length_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 2) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p082_prime_length_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i * i )) ”
.

Definition p082_prime_length_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((i * i ) <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((len <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition p082_prime_length_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((i * i ) <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p082_prime_length_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((len % ( i ) ) = 0) ” 
  &&  “ ((i * i ) <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p082_prime_length_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 46340) ” 
  &&  “ (i <= len) ” 
  &&  “ (prime_prefix (i + 1 ) len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p082_prime_length_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((i * i ) > len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p082_prime_length_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 2) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 46340) ” 
  &&  “ (2 <= (len + 1 )) ” 
  &&  “ (prime_prefix 2 len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_entail_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((len % ( i ) ) <> 0) ” 
  &&  “ ((i * i ) <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 46340) ” 
  &&  “ (i <= len) ” 
  &&  “ (prime_prefix (i + 1 ) len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_entail_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < 46340) ” 
  &&  “ (i <= len) ” 
  &&  “ (prime_prefix (i + 1 ) len ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 46340) ” 
  &&  “ ((i + 1 ) <= (len + 1 )) ” 
  &&  “ (prime_prefix (i + 1 ) len ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((i * i ) > len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_82_spec l 1 ) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_return_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((len % ( i ) ) = 0) ” 
  &&  “ ((i * i ) <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (2 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= 46340) ” 
  &&  “ (i <= (len + 1 )) ” 
  &&  “ (prime_prefix i len ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_82_spec l 0 ) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_return_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 2) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_82_spec l 0 ) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_partial_solve_wit_1_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p082_prime_length_partial_solve_wit_1_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len <= 2147302921) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_82_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p082_prime_length_partial_solve_wit_1 := p082_prime_length_partial_solve_wit_1_pure -> p082_prime_length_partial_solve_wit_1_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p082_prime_length_safety_wit_1 : p082_prime_length_safety_wit_1.
Axiom proof_of_p082_prime_length_safety_wit_2 : p082_prime_length_safety_wit_2.
Axiom proof_of_p082_prime_length_safety_wit_3 : p082_prime_length_safety_wit_3.
Axiom proof_of_p082_prime_length_safety_wit_4 : p082_prime_length_safety_wit_4.
Axiom proof_of_p082_prime_length_safety_wit_5 : p082_prime_length_safety_wit_5.
Axiom proof_of_p082_prime_length_safety_wit_6 : p082_prime_length_safety_wit_6.
Axiom proof_of_p082_prime_length_safety_wit_7 : p082_prime_length_safety_wit_7.
Axiom proof_of_p082_prime_length_safety_wit_8 : p082_prime_length_safety_wit_8.
Axiom proof_of_p082_prime_length_safety_wit_9 : p082_prime_length_safety_wit_9.
Axiom proof_of_p082_prime_length_entail_wit_1 : p082_prime_length_entail_wit_1.
Axiom proof_of_p082_prime_length_entail_wit_2 : p082_prime_length_entail_wit_2.
Axiom proof_of_p082_prime_length_entail_wit_3 : p082_prime_length_entail_wit_3.
Axiom proof_of_p082_prime_length_return_wit_1 : p082_prime_length_return_wit_1.
Axiom proof_of_p082_prime_length_return_wit_2 : p082_prime_length_return_wit_2.
Axiom proof_of_p082_prime_length_return_wit_3 : p082_prime_length_return_wit_3.
Axiom proof_of_p082_prime_length_partial_solve_wit_1_pure : p082_prime_length_partial_solve_wit_1_pure.
Axiom proof_of_p082_prime_length_partial_solve_wit_1 : p082_prime_length_partial_solve_wit_1.

End VC_Correct.
