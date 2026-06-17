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
Require Import p107_even_odd_palindrome.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function is_pal -----*)

Definition is_pal_safety_wit_1 := 
forall (x_pre: Z) (x0: Z) ,
  “ (x_pre = x0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ”
  &&  ((( &( "r" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_pal_safety_wit_2 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_pal_safety_wit_3 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ (((r * 10 ) + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((r * 10 ) + (t % ( 10 ) ) )) ”
.

Definition is_pal_safety_wit_4 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition is_pal_safety_wit_5 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ ((r * 10 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r * 10 )) ”
.

Definition is_pal_safety_wit_6 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_safety_wit_7 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> r)
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_safety_wit_8 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> ((r * 10 ) + (t % ( 10 ) ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition is_pal_safety_wit_9 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
  **  ((( &( "r" ) )) # Int  |-> ((r * 10 ) + (t % ( 10 ) ) ))
  **  ((( &( "t" ) )) # Int  |-> t)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition is_pal_entail_wit_1 := 
forall (x_pre: Z) (x0: Z) ,
  “ (x_pre = x0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 x_pre 0 ) ”
  &&  ((( &( "x" ) )) # Int  |-> x0)
.

Definition is_pal_entail_wit_2 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (t > 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  emp
|--
  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 (t ÷ 10 ) ((r * 10 ) + (t % ( 10 ) ) ) ) ”
  &&  emp
.

Definition is_pal_return_wit_1 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (r = x0) ” 
  &&  “ (t <= 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  emp
|--
  “ (1 = (is_pal_model (x0))) ”
  &&  emp
.

Definition is_pal_return_wit_2 := 
forall (x0: Z) (t: Z) (r: Z) ,
  “ (r <> x0) ” 
  &&  “ (t <= 0) ” 
  &&  “ (1 <= x0) ” 
  &&  “ (x0 <= 1000) ” 
  &&  “ (pal_reverse_loop_state x0 t r ) ”
  &&  emp
|--
  “ (0 = (is_pal_model (x0))) ”
  &&  emp
.

(*----- Function p107_even_odd_palindrome -----*)

Definition p107_even_odd_palindrome_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) ,
  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  ((( &( "num2" ) )) # Int  |->_)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) ,
  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  ((( &( "num1" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "num2" ) )) # Int  |-> 0)
  **  ((( &( "num1" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p107_even_odd_palindrome_safety_wit_4 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_5 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_6 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p107_even_odd_palindrome_safety_wit_7 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((num1 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num1 + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_8 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p107_even_odd_palindrome_safety_wit_9 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_10 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_11 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_12 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_13 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_14 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_15 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_16 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_17 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_18 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ False ”
.

Definition p107_even_odd_palindrome_safety_wit_19 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ False ”
.

Definition p107_even_odd_palindrome_safety_wit_20 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ False ”
.

Definition p107_even_odd_palindrome_safety_wit_21 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ False ”
.

Definition p107_even_odd_palindrome_safety_wit_22 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ False ”
.

Definition p107_even_odd_palindrome_safety_wit_23 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((num2 + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (num2 + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_24 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p107_even_odd_palindrome_safety_wit_25 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_26 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_27 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_28 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> (num2 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p107_even_odd_palindrome_safety_wit_29 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) ,
  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_30 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p107_even_odd_palindrome_safety_wit_31 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "data" ) )) # Ptr  |-> retval)
  **  (IntArray.undef_full retval 2 )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p107_even_odd_palindrome_safety_wit_32 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  (IntArray.undef_seg retval 1 2 )
  **  ((( &( "data" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p107_even_odd_palindrome_entail_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (retval <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (1 - 1 ) n0 0 0 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_entail_wit_2_1 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 (num1 + 1 ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 (num1 + 1 ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
.

Definition p107_even_odd_palindrome_entail_wit_2_2 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  (EX (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
.

Definition p107_even_odd_palindrome_entail_wit_2_3 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  (EX (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
.

Definition p107_even_odd_palindrome_entail_wit_2_4 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  (EX (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (“ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
.

Definition p107_even_odd_palindrome_entail_wit_2_5 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  (“ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_3: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 (num1 + 1 ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
  ||
  (EX (retval_4: Z) ,
  “ (retval_4 = 0) ” 
  &&  “ (retval_4 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 (num1 + 1 ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_))
.

Definition p107_even_odd_palindrome_entail_wit_3_1 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix ((i + 1 ) - 1 ) n0 (num2 + 1 ) num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_entail_wit_3_2 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix ((i + 1 ) - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_entail_wit_3_3 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix ((i + 1 ) - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_entail_wit_3_4 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) (retval_2: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = (is_pal_model (i))) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix ((i + 1 ) - 1 ) n0 num2 (num1 + 1 ) ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_return_wit_1 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |-> num1)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = 2) ” 
  &&  “ (output_l = (cons ((Znth (0) (output_l) (0))) ((cons ((Znth (1) (output_l) (0))) (nil))))) ” 
  &&  “ (problem_107_spec n0 output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition p107_even_odd_palindrome_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) ,
  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  emp
|--
  “ (n_pre = n0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ”
  &&  emp
.

Definition p107_even_odd_palindrome_partial_solve_wit_2_pure := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) ,
  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ”
.

Definition p107_even_odd_palindrome_partial_solve_wit_2_aux := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) ,
  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_partial_solve_wit_2 := p107_even_odd_palindrome_partial_solve_wit_2_pure -> p107_even_odd_palindrome_partial_solve_wit_2_aux.

Definition p107_even_odd_palindrome_partial_solve_wit_3_pure := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ”
.

Definition p107_even_odd_palindrome_partial_solve_wit_3_aux := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ” 
  &&  “ ((i % ( 2 ) ) <> 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_partial_solve_wit_3 := p107_even_odd_palindrome_partial_solve_wit_3_pure -> p107_even_odd_palindrome_partial_solve_wit_3_aux.

Definition p107_even_odd_palindrome_partial_solve_wit_4_pure := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ”
.

Definition p107_even_odd_palindrome_partial_solve_wit_4_aux := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ” 
  &&  “ (retval = 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_partial_solve_wit_4 := p107_even_odd_palindrome_partial_solve_wit_4_pure -> p107_even_odd_palindrome_partial_solve_wit_4_aux.

Definition p107_even_odd_palindrome_partial_solve_wit_5_pure := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> (num1 + 1 ))
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ”
.

Definition p107_even_odd_palindrome_partial_solve_wit_5_aux := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (i = i) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= 1000) ” 
  &&  “ ((i % ( 2 ) ) = 1) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = (is_pal_model (i))) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_partial_solve_wit_5 := p107_even_odd_palindrome_partial_solve_wit_5_pure -> p107_even_odd_palindrome_partial_solve_wit_5_aux.

Definition p107_even_odd_palindrome_partial_solve_wit_6_pure := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) ,
  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "num1" ) )) # Int  |-> num1)
  **  ((( &( "num2" ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ”
.

Definition p107_even_odd_palindrome_partial_solve_wit_6_aux := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) ,
  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
|--
  “ (2 >= 0) ” 
  &&  “ (2 < INT_MAX) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
.

Definition p107_even_odd_palindrome_partial_solve_wit_6 := p107_even_odd_palindrome_partial_solve_wit_6_pure -> p107_even_odd_palindrome_partial_solve_wit_6_aux.

Definition p107_even_odd_palindrome_partial_solve_wit_7 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (IntArray.undef_full retval 2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval 1 2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Definition p107_even_odd_palindrome_partial_solve_wit_8 := 
forall (n0: Z) (num2: Z) (num1: Z) (i: Z) (out: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (((retval + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  (IntArray.undef_seg retval 1 2 )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
|--
  “ (retval <> 0) ” 
  &&  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ (n0 <= 1000) ” 
  &&  “ (problem_107_pre n0 ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ (pal_count_prefix (i - 1 ) n0 num2 num1 ) ”
  &&  (((retval + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (((retval + (0 * sizeof(INT) ) )) # Int  |-> num2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> 2)
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_is_pal_safety_wit_1 : is_pal_safety_wit_1.
Axiom proof_of_is_pal_safety_wit_2 : is_pal_safety_wit_2.
Axiom proof_of_is_pal_safety_wit_3 : is_pal_safety_wit_3.
Axiom proof_of_is_pal_safety_wit_4 : is_pal_safety_wit_4.
Axiom proof_of_is_pal_safety_wit_5 : is_pal_safety_wit_5.
Axiom proof_of_is_pal_safety_wit_6 : is_pal_safety_wit_6.
Axiom proof_of_is_pal_safety_wit_7 : is_pal_safety_wit_7.
Axiom proof_of_is_pal_safety_wit_8 : is_pal_safety_wit_8.
Axiom proof_of_is_pal_safety_wit_9 : is_pal_safety_wit_9.
Axiom proof_of_is_pal_entail_wit_1 : is_pal_entail_wit_1.
Axiom proof_of_is_pal_entail_wit_2 : is_pal_entail_wit_2.
Axiom proof_of_is_pal_return_wit_1 : is_pal_return_wit_1.
Axiom proof_of_is_pal_return_wit_2 : is_pal_return_wit_2.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_1 : p107_even_odd_palindrome_safety_wit_1.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_2 : p107_even_odd_palindrome_safety_wit_2.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_3 : p107_even_odd_palindrome_safety_wit_3.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_4 : p107_even_odd_palindrome_safety_wit_4.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_5 : p107_even_odd_palindrome_safety_wit_5.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_6 : p107_even_odd_palindrome_safety_wit_6.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_7 : p107_even_odd_palindrome_safety_wit_7.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_8 : p107_even_odd_palindrome_safety_wit_8.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_9 : p107_even_odd_palindrome_safety_wit_9.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_10 : p107_even_odd_palindrome_safety_wit_10.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_11 : p107_even_odd_palindrome_safety_wit_11.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_12 : p107_even_odd_palindrome_safety_wit_12.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_13 : p107_even_odd_palindrome_safety_wit_13.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_14 : p107_even_odd_palindrome_safety_wit_14.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_15 : p107_even_odd_palindrome_safety_wit_15.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_16 : p107_even_odd_palindrome_safety_wit_16.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_17 : p107_even_odd_palindrome_safety_wit_17.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_18 : p107_even_odd_palindrome_safety_wit_18.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_19 : p107_even_odd_palindrome_safety_wit_19.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_20 : p107_even_odd_palindrome_safety_wit_20.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_21 : p107_even_odd_palindrome_safety_wit_21.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_22 : p107_even_odd_palindrome_safety_wit_22.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_23 : p107_even_odd_palindrome_safety_wit_23.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_24 : p107_even_odd_palindrome_safety_wit_24.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_25 : p107_even_odd_palindrome_safety_wit_25.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_26 : p107_even_odd_palindrome_safety_wit_26.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_27 : p107_even_odd_palindrome_safety_wit_27.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_28 : p107_even_odd_palindrome_safety_wit_28.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_29 : p107_even_odd_palindrome_safety_wit_29.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_30 : p107_even_odd_palindrome_safety_wit_30.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_31 : p107_even_odd_palindrome_safety_wit_31.
Axiom proof_of_p107_even_odd_palindrome_safety_wit_32 : p107_even_odd_palindrome_safety_wit_32.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_1 : p107_even_odd_palindrome_entail_wit_1.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_2_1 : p107_even_odd_palindrome_entail_wit_2_1.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_2_2 : p107_even_odd_palindrome_entail_wit_2_2.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_2_3 : p107_even_odd_palindrome_entail_wit_2_3.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_2_4 : p107_even_odd_palindrome_entail_wit_2_4.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_2_5 : p107_even_odd_palindrome_entail_wit_2_5.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_3_1 : p107_even_odd_palindrome_entail_wit_3_1.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_3_2 : p107_even_odd_palindrome_entail_wit_3_2.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_3_3 : p107_even_odd_palindrome_entail_wit_3_3.
Axiom proof_of_p107_even_odd_palindrome_entail_wit_3_4 : p107_even_odd_palindrome_entail_wit_3_4.
Axiom proof_of_p107_even_odd_palindrome_return_wit_1 : p107_even_odd_palindrome_return_wit_1.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_1 : p107_even_odd_palindrome_partial_solve_wit_1.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_2_pure : p107_even_odd_palindrome_partial_solve_wit_2_pure.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_2 : p107_even_odd_palindrome_partial_solve_wit_2.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_3_pure : p107_even_odd_palindrome_partial_solve_wit_3_pure.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_3 : p107_even_odd_palindrome_partial_solve_wit_3.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_4_pure : p107_even_odd_palindrome_partial_solve_wit_4_pure.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_4 : p107_even_odd_palindrome_partial_solve_wit_4.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_5_pure : p107_even_odd_palindrome_partial_solve_wit_5_pure.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_5 : p107_even_odd_palindrome_partial_solve_wit_5.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_6_pure : p107_even_odd_palindrome_partial_solve_wit_6_pure.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_6 : p107_even_odd_palindrome_partial_solve_wit_6.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_7 : p107_even_odd_palindrome_partial_solve_wit_7.
Axiom proof_of_p107_even_odd_palindrome_partial_solve_wit_8 : p107_even_odd_palindrome_partial_solve_wit_8.

End VC_Correct.
