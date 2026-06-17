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
Require Import p067_fruit_distribution.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p067_fruit_distribution -----*)

Definition p067_fruit_distribution_safety_wit_1 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "num1" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_2 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "num1" ) )) # Int  |->_)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_3 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_4 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_5 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_6 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_7 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "slen" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_8 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p067_fruit_distribution_safety_wit_9 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition p067_fruit_distribution_safety_wit_10 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_11 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_12 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) )) ”
.

Definition p067_fruit_distribution_safety_wit_13 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 )) ”
.

Definition p067_fruit_distribution_safety_wit_14 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((cur * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur * 10 )) ”
.

Definition p067_fruit_distribution_safety_wit_15 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p067_fruit_distribution_safety_wit_16 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p067_fruit_distribution_safety_wit_17 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> 0)
|--
  “ (((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) )) ”
.

Definition p067_fruit_distribution_safety_wit_18 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> 0)
|--
  “ (((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 )) ”
.

Definition p067_fruit_distribution_safety_wit_19 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> 0)
|--
  “ ((0 * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (0 * 10 )) ”
.

Definition p067_fruit_distribution_safety_wit_20 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> 0)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p067_fruit_distribution_safety_wit_21 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> 0)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p067_fruit_distribution_safety_wit_22 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_23 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_24 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_25 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_26 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_27 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_28 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_29 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_30 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_31 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_32 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_33 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_34 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_35 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_36 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_37 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_38 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <> (INT_MIN)) ”
.

Definition p067_fruit_distribution_safety_wit_39 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p067_fruit_distribution_safety_wit_40 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_41 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_42 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_43 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_44 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_45 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_46 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_47 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_48 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> ((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_49 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> ((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p067_fruit_distribution_safety_wit_50 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_51 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_52 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_53 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_54 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_55 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_56 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_57 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p067_fruit_distribution_safety_wit_58 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p067_fruit_distribution_safety_wit_59 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p067_fruit_distribution_safety_wit_60 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_61 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_62 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_63 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_64 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_65 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_66 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p067_fruit_distribution_safety_wit_67 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p067_fruit_distribution_safety_wit_68 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_69 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_70 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p067_fruit_distribution_safety_wit_71 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - 0 ) - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - 0 ) - 0 )) ”
.

Definition p067_fruit_distribution_safety_wit_72 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - num1 ) - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - num1 ) - 0 )) ”
.

Definition p067_fruit_distribution_safety_wit_73 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - cur ) - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - cur ) - 0 )) ”
.

Definition p067_fruit_distribution_safety_wit_74 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - cur ) - num2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - cur ) - num2 )) ”
.

Definition p067_fruit_distribution_safety_wit_75 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - num1 ) - cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - num1 ) - cur )) ”
.

Definition p067_fruit_distribution_safety_wit_76 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - num1 ) - num2 )) ”
.

Definition p067_fruit_distribution_safety_wit_77 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - num1 ) - num2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - num1 ) - num2 )) ”
.

Definition p067_fruit_distribution_safety_wit_78 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((total_pre - 0 ) - num2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((total_pre - 0 ) - num2 )) ”
.

Definition p067_fruit_distribution_safety_wit_79 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - 0 )) ”
.

Definition p067_fruit_distribution_safety_wit_80 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - num1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - num1 )) ”
.

Definition p067_fruit_distribution_safety_wit_81 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - cur )) ”
.

Definition p067_fruit_distribution_safety_wit_82 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> cur)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - cur )) ”
.

Definition p067_fruit_distribution_safety_wit_83 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> cur)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - num1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - num1 )) ”
.

Definition p067_fruit_distribution_safety_wit_84 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - num1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - num1 )) ”
.

Definition p067_fruit_distribution_safety_wit_85 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - num1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - num1 )) ”
.

Definition p067_fruit_distribution_safety_wit_86 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "slen" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((total_pre - 0 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (total_pre - 0 )) ”
.

Definition p067_fruit_distribution_entail_wit_1 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "slen" ) )) # Int  |-> retval)
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((-1) = (fruit_num1_prefix (0) (l))) ” 
  &&  “ ((-1) = (fruit_num2_prefix (0) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix (0) (l))) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  ((( &( "slen" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_1 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ (((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= ((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) )) ” 
  &&  “ (((cur * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_2 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ (((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= ((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) )) ” 
  &&  “ (((0 * 10 ) + ((Znth i (app (l) ((cons (0) (nil)))) 0) - 48 ) ) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_3 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_4 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_5 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (cur = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_6 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (cur = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_7 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (cur = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_8 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (cur = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= (-1)) ” 
  &&  “ ((-1) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_9 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_entail_wit_2_10 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix ((i + 1 )) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix ((i + 1 )) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix ((i + 1 )) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_1 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - 0 ) - 0 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_2 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - num1 ) - 0 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_3 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - cur ) - 0 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_4 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - cur ) - num2 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_5 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (cur >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 < 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - num1 ) - cur ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_6 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur >= 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - num1 ) - num2 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_7 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 >= 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - num1 ) - num2 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_return_wit_8 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (num2 >= 0) ” 
  &&  “ (num1 < 0) ” 
  &&  “ (cur < 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_67_spec l total_pre ((total_pre - 0 ) - num2 ) ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_partial_solve_wit_1_pure := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "slen" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> (-1))
  **  ((( &( "num2" ) )) # Int  |-> (-1))
  **  ((( &( "num1" ) )) # Int  |-> (-1))
  **  ((( &( "total" ) )) # Int  |-> total_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p067_fruit_distribution_partial_solve_wit_1_aux := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p067_fruit_distribution_partial_solve_wit_1 := p067_fruit_distribution_partial_solve_wit_1_pure -> p067_fruit_distribution_partial_solve_wit_1_aux.

Definition p067_fruit_distribution_partial_solve_wit_2 := 
forall (total_pre: Z) (s_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (num2: Z) (num1: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (0 <= total_pre) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_67_pre l total_pre ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (fruit_state_safe l ) ” 
  &&  “ (fruit_output_safe l total_pre ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (num1 = (fruit_num1_prefix (i) (l))) ” 
  &&  “ (num2 = (fruit_num2_prefix (i) (l))) ” 
  &&  “ (cur = (fruit_cur_prefix (i) (l))) ” 
  &&  “ ((-1) <= num1) ” 
  &&  “ (num1 <= INT_MAX) ” 
  &&  “ ((-1) <= num2) ” 
  &&  “ (num2 <= INT_MAX) ” 
  &&  “ ((-1) <= cur) ” 
  &&  “ (cur <= INT_MAX) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p067_fruit_distribution_safety_wit_1 : p067_fruit_distribution_safety_wit_1.
Axiom proof_of_p067_fruit_distribution_safety_wit_2 : p067_fruit_distribution_safety_wit_2.
Axiom proof_of_p067_fruit_distribution_safety_wit_3 : p067_fruit_distribution_safety_wit_3.
Axiom proof_of_p067_fruit_distribution_safety_wit_4 : p067_fruit_distribution_safety_wit_4.
Axiom proof_of_p067_fruit_distribution_safety_wit_5 : p067_fruit_distribution_safety_wit_5.
Axiom proof_of_p067_fruit_distribution_safety_wit_6 : p067_fruit_distribution_safety_wit_6.
Axiom proof_of_p067_fruit_distribution_safety_wit_7 : p067_fruit_distribution_safety_wit_7.
Axiom proof_of_p067_fruit_distribution_safety_wit_8 : p067_fruit_distribution_safety_wit_8.
Axiom proof_of_p067_fruit_distribution_safety_wit_9 : p067_fruit_distribution_safety_wit_9.
Axiom proof_of_p067_fruit_distribution_safety_wit_10 : p067_fruit_distribution_safety_wit_10.
Axiom proof_of_p067_fruit_distribution_safety_wit_11 : p067_fruit_distribution_safety_wit_11.
Axiom proof_of_p067_fruit_distribution_safety_wit_12 : p067_fruit_distribution_safety_wit_12.
Axiom proof_of_p067_fruit_distribution_safety_wit_13 : p067_fruit_distribution_safety_wit_13.
Axiom proof_of_p067_fruit_distribution_safety_wit_14 : p067_fruit_distribution_safety_wit_14.
Axiom proof_of_p067_fruit_distribution_safety_wit_15 : p067_fruit_distribution_safety_wit_15.
Axiom proof_of_p067_fruit_distribution_safety_wit_16 : p067_fruit_distribution_safety_wit_16.
Axiom proof_of_p067_fruit_distribution_safety_wit_17 : p067_fruit_distribution_safety_wit_17.
Axiom proof_of_p067_fruit_distribution_safety_wit_18 : p067_fruit_distribution_safety_wit_18.
Axiom proof_of_p067_fruit_distribution_safety_wit_19 : p067_fruit_distribution_safety_wit_19.
Axiom proof_of_p067_fruit_distribution_safety_wit_20 : p067_fruit_distribution_safety_wit_20.
Axiom proof_of_p067_fruit_distribution_safety_wit_21 : p067_fruit_distribution_safety_wit_21.
Axiom proof_of_p067_fruit_distribution_safety_wit_22 : p067_fruit_distribution_safety_wit_22.
Axiom proof_of_p067_fruit_distribution_safety_wit_23 : p067_fruit_distribution_safety_wit_23.
Axiom proof_of_p067_fruit_distribution_safety_wit_24 : p067_fruit_distribution_safety_wit_24.
Axiom proof_of_p067_fruit_distribution_safety_wit_25 : p067_fruit_distribution_safety_wit_25.
Axiom proof_of_p067_fruit_distribution_safety_wit_26 : p067_fruit_distribution_safety_wit_26.
Axiom proof_of_p067_fruit_distribution_safety_wit_27 : p067_fruit_distribution_safety_wit_27.
Axiom proof_of_p067_fruit_distribution_safety_wit_28 : p067_fruit_distribution_safety_wit_28.
Axiom proof_of_p067_fruit_distribution_safety_wit_29 : p067_fruit_distribution_safety_wit_29.
Axiom proof_of_p067_fruit_distribution_safety_wit_30 : p067_fruit_distribution_safety_wit_30.
Axiom proof_of_p067_fruit_distribution_safety_wit_31 : p067_fruit_distribution_safety_wit_31.
Axiom proof_of_p067_fruit_distribution_safety_wit_32 : p067_fruit_distribution_safety_wit_32.
Axiom proof_of_p067_fruit_distribution_safety_wit_33 : p067_fruit_distribution_safety_wit_33.
Axiom proof_of_p067_fruit_distribution_safety_wit_34 : p067_fruit_distribution_safety_wit_34.
Axiom proof_of_p067_fruit_distribution_safety_wit_35 : p067_fruit_distribution_safety_wit_35.
Axiom proof_of_p067_fruit_distribution_safety_wit_36 : p067_fruit_distribution_safety_wit_36.
Axiom proof_of_p067_fruit_distribution_safety_wit_37 : p067_fruit_distribution_safety_wit_37.
Axiom proof_of_p067_fruit_distribution_safety_wit_38 : p067_fruit_distribution_safety_wit_38.
Axiom proof_of_p067_fruit_distribution_safety_wit_39 : p067_fruit_distribution_safety_wit_39.
Axiom proof_of_p067_fruit_distribution_safety_wit_40 : p067_fruit_distribution_safety_wit_40.
Axiom proof_of_p067_fruit_distribution_safety_wit_41 : p067_fruit_distribution_safety_wit_41.
Axiom proof_of_p067_fruit_distribution_safety_wit_42 : p067_fruit_distribution_safety_wit_42.
Axiom proof_of_p067_fruit_distribution_safety_wit_43 : p067_fruit_distribution_safety_wit_43.
Axiom proof_of_p067_fruit_distribution_safety_wit_44 : p067_fruit_distribution_safety_wit_44.
Axiom proof_of_p067_fruit_distribution_safety_wit_45 : p067_fruit_distribution_safety_wit_45.
Axiom proof_of_p067_fruit_distribution_safety_wit_46 : p067_fruit_distribution_safety_wit_46.
Axiom proof_of_p067_fruit_distribution_safety_wit_47 : p067_fruit_distribution_safety_wit_47.
Axiom proof_of_p067_fruit_distribution_safety_wit_48 : p067_fruit_distribution_safety_wit_48.
Axiom proof_of_p067_fruit_distribution_safety_wit_49 : p067_fruit_distribution_safety_wit_49.
Axiom proof_of_p067_fruit_distribution_safety_wit_50 : p067_fruit_distribution_safety_wit_50.
Axiom proof_of_p067_fruit_distribution_safety_wit_51 : p067_fruit_distribution_safety_wit_51.
Axiom proof_of_p067_fruit_distribution_safety_wit_52 : p067_fruit_distribution_safety_wit_52.
Axiom proof_of_p067_fruit_distribution_safety_wit_53 : p067_fruit_distribution_safety_wit_53.
Axiom proof_of_p067_fruit_distribution_safety_wit_54 : p067_fruit_distribution_safety_wit_54.
Axiom proof_of_p067_fruit_distribution_safety_wit_55 : p067_fruit_distribution_safety_wit_55.
Axiom proof_of_p067_fruit_distribution_safety_wit_56 : p067_fruit_distribution_safety_wit_56.
Axiom proof_of_p067_fruit_distribution_safety_wit_57 : p067_fruit_distribution_safety_wit_57.
Axiom proof_of_p067_fruit_distribution_safety_wit_58 : p067_fruit_distribution_safety_wit_58.
Axiom proof_of_p067_fruit_distribution_safety_wit_59 : p067_fruit_distribution_safety_wit_59.
Axiom proof_of_p067_fruit_distribution_safety_wit_60 : p067_fruit_distribution_safety_wit_60.
Axiom proof_of_p067_fruit_distribution_safety_wit_61 : p067_fruit_distribution_safety_wit_61.
Axiom proof_of_p067_fruit_distribution_safety_wit_62 : p067_fruit_distribution_safety_wit_62.
Axiom proof_of_p067_fruit_distribution_safety_wit_63 : p067_fruit_distribution_safety_wit_63.
Axiom proof_of_p067_fruit_distribution_safety_wit_64 : p067_fruit_distribution_safety_wit_64.
Axiom proof_of_p067_fruit_distribution_safety_wit_65 : p067_fruit_distribution_safety_wit_65.
Axiom proof_of_p067_fruit_distribution_safety_wit_66 : p067_fruit_distribution_safety_wit_66.
Axiom proof_of_p067_fruit_distribution_safety_wit_67 : p067_fruit_distribution_safety_wit_67.
Axiom proof_of_p067_fruit_distribution_safety_wit_68 : p067_fruit_distribution_safety_wit_68.
Axiom proof_of_p067_fruit_distribution_safety_wit_69 : p067_fruit_distribution_safety_wit_69.
Axiom proof_of_p067_fruit_distribution_safety_wit_70 : p067_fruit_distribution_safety_wit_70.
Axiom proof_of_p067_fruit_distribution_safety_wit_71 : p067_fruit_distribution_safety_wit_71.
Axiom proof_of_p067_fruit_distribution_safety_wit_72 : p067_fruit_distribution_safety_wit_72.
Axiom proof_of_p067_fruit_distribution_safety_wit_73 : p067_fruit_distribution_safety_wit_73.
Axiom proof_of_p067_fruit_distribution_safety_wit_74 : p067_fruit_distribution_safety_wit_74.
Axiom proof_of_p067_fruit_distribution_safety_wit_75 : p067_fruit_distribution_safety_wit_75.
Axiom proof_of_p067_fruit_distribution_safety_wit_76 : p067_fruit_distribution_safety_wit_76.
Axiom proof_of_p067_fruit_distribution_safety_wit_77 : p067_fruit_distribution_safety_wit_77.
Axiom proof_of_p067_fruit_distribution_safety_wit_78 : p067_fruit_distribution_safety_wit_78.
Axiom proof_of_p067_fruit_distribution_safety_wit_79 : p067_fruit_distribution_safety_wit_79.
Axiom proof_of_p067_fruit_distribution_safety_wit_80 : p067_fruit_distribution_safety_wit_80.
Axiom proof_of_p067_fruit_distribution_safety_wit_81 : p067_fruit_distribution_safety_wit_81.
Axiom proof_of_p067_fruit_distribution_safety_wit_82 : p067_fruit_distribution_safety_wit_82.
Axiom proof_of_p067_fruit_distribution_safety_wit_83 : p067_fruit_distribution_safety_wit_83.
Axiom proof_of_p067_fruit_distribution_safety_wit_84 : p067_fruit_distribution_safety_wit_84.
Axiom proof_of_p067_fruit_distribution_safety_wit_85 : p067_fruit_distribution_safety_wit_85.
Axiom proof_of_p067_fruit_distribution_safety_wit_86 : p067_fruit_distribution_safety_wit_86.
Axiom proof_of_p067_fruit_distribution_entail_wit_1 : p067_fruit_distribution_entail_wit_1.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_1 : p067_fruit_distribution_entail_wit_2_1.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_2 : p067_fruit_distribution_entail_wit_2_2.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_3 : p067_fruit_distribution_entail_wit_2_3.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_4 : p067_fruit_distribution_entail_wit_2_4.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_5 : p067_fruit_distribution_entail_wit_2_5.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_6 : p067_fruit_distribution_entail_wit_2_6.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_7 : p067_fruit_distribution_entail_wit_2_7.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_8 : p067_fruit_distribution_entail_wit_2_8.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_9 : p067_fruit_distribution_entail_wit_2_9.
Axiom proof_of_p067_fruit_distribution_entail_wit_2_10 : p067_fruit_distribution_entail_wit_2_10.
Axiom proof_of_p067_fruit_distribution_return_wit_1 : p067_fruit_distribution_return_wit_1.
Axiom proof_of_p067_fruit_distribution_return_wit_2 : p067_fruit_distribution_return_wit_2.
Axiom proof_of_p067_fruit_distribution_return_wit_3 : p067_fruit_distribution_return_wit_3.
Axiom proof_of_p067_fruit_distribution_return_wit_4 : p067_fruit_distribution_return_wit_4.
Axiom proof_of_p067_fruit_distribution_return_wit_5 : p067_fruit_distribution_return_wit_5.
Axiom proof_of_p067_fruit_distribution_return_wit_6 : p067_fruit_distribution_return_wit_6.
Axiom proof_of_p067_fruit_distribution_return_wit_7 : p067_fruit_distribution_return_wit_7.
Axiom proof_of_p067_fruit_distribution_return_wit_8 : p067_fruit_distribution_return_wit_8.
Axiom proof_of_p067_fruit_distribution_partial_solve_wit_1_pure : p067_fruit_distribution_partial_solve_wit_1_pure.
Axiom proof_of_p067_fruit_distribution_partial_solve_wit_1 : p067_fruit_distribution_partial_solve_wit_1.
Axiom proof_of_p067_fruit_distribution_partial_solve_wit_2 : p067_fruit_distribution_partial_solve_wit_2.

End VC_Correct.
