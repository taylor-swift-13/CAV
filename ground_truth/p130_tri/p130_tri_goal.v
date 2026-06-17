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
Require Import p130_tri.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import int_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import undef_uint_array_strategy_proof.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import array_shape_strategy_proof.

(*----- Function p130_tri -----*)

Definition p130_tri_safety_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition p130_tri_safety_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition p130_tri_safety_wit_4 := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_5 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p130_tri_safety_wit_6 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_7 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p130_tri_safety_wit_8 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_9 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p130_tri_safety_wit_10 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> 3)
  **  (IntArray.undef_seg retval_2 (1 + 1 ) (n_pre + 1 ) )
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  ((( &( "data" ) )) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p130_tri_safety_wit_11 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p130_tri_safety_wit_12 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p130_tri_safety_wit_13 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p130_tri_safety_wit_14 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((1 + (i ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (1 + (i ÷ 2 ) )) ”
.

Definition p130_tri_safety_wit_15 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p130_tri_safety_wit_16 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_17 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p130_tri_safety_wit_18 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (((((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) ”
.

Definition p130_tri_safety_wit_19 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (((i + 1 ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p130_tri_safety_wit_20 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p130_tri_safety_wit_21 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 )) ”
.

Definition p130_tri_safety_wit_22 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) )) ”
.

Definition p130_tri_safety_wit_23 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition p130_tri_safety_wit_24 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition p130_tri_safety_wit_25 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_26 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p130_tri_safety_wit_27 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_28 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p130_tri_safety_wit_29 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p130_tri_safety_wit_30 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app ((sublist (0) (i) ((tri_sequence (n0))))) ((cons (((((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p130_tri_safety_wit_31 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app ((sublist (0) (i) ((tri_sequence (n0))))) ((cons ((1 + (i ÷ 2 ) )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  ((( &( "n" ) )) # Int  |-> n0)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "data" ) )) # Ptr  |-> data)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p130_tri_entail_wit_1 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |-> 3)
  **  (IntArray.undef_seg retval_2 (1 + 1 ) (n_pre + 1 ) )
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (retval <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((( &( "n" ) )) # Int  |-> n0)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg retval_2 0 2 (sublist (0) (2) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg retval_2 2 (n0 + 1 ) )
.

Definition p130_tri_entail_wit_2_1 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app ((sublist (0) (i) ((tri_sequence (n0))))) ((cons ((1 + (i ÷ 2 ) )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 (i + 1 ) (sublist (0) ((i + 1 )) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
.

Definition p130_tri_entail_wit_2_2 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 (i + 1 ) (app ((sublist (0) (i) ((tri_sequence (n0))))) ((cons (((((Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) + (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0) ) + 1 ) + ((i + 1 ) ÷ 2 ) )) (nil)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
|--
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 (i + 1 ) (sublist (0) ((i + 1 )) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
.

Definition p130_tri_return_wit_1 := 
forall (n0: Z) (i: Z) (data_2: Z) (out: Z) ,
  “ (i > n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data_2 <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data_2)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data_2 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data_2 i (n0 + 1 ) )
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = (n0 + 1 )) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (tri_sequence (n0))) ” 
  &&  “ (problem_130_spec n0 output_l ) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition p130_tri_return_wit_2 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
|--
  EX (output_l: (@list Z))  (output_size: Z)  (data: Z) ,
  “ (retval <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (output_size = (n0 + 1 )) ” 
  &&  “ (output_size = (Zlength (output_l))) ” 
  &&  “ (output_l = (tri_sequence (n0))) ” 
  &&  “ (problem_130_spec n0 output_l ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> output_size)
  **  (IntArray.full data output_size output_l )
.

Definition p130_tri_partial_solve_wit_1 := 
forall (n_pre: Z) (n0: Z) ,
  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  emp
|--
  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  emp
.

Definition p130_tri_partial_solve_wit_2_pure := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) >= 0) ” 
  &&  “ ((n_pre + 1 ) < INT_MAX) ”
.

Definition p130_tri_partial_solve_wit_2_aux := 
forall (n_pre: Z) (n0: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
|--
  “ ((n_pre + 1 ) >= 0) ” 
  &&  “ ((n_pre + 1 ) < INT_MAX) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |->_)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
.

Definition p130_tri_partial_solve_wit_2 := p130_tri_partial_solve_wit_2_pure -> p130_tri_partial_solve_wit_2_aux.

Definition p130_tri_partial_solve_wit_3 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (IntArray.undef_full retval_2 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
|--
  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
.

Definition p130_tri_partial_solve_wit_4 := 
forall (n_pre: Z) (n0: Z) (retval: Z) (retval_2: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  (IntArray.undef_seg retval_2 1 (n_pre + 1 ) )
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
|--
  “ (n_pre <> 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (n_pre = n0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ”
  &&  (((retval_2 + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg retval_2 (1 + 1 ) (n_pre + 1 ) )
  **  (((retval_2 + (0 * sizeof(INT) ) )) # Int  |-> 1)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> retval_2)
  **  ((&((retval)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n_pre + 1 ))
.

Definition p130_tri_partial_solve_wit_5 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i % ( 2 ) ) = 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
.

Definition p130_tri_partial_solve_wit_6 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (((data + ((i - 1 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 1 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0))
  **  (IntArray.missing_i data (i - 1 ) 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
.

Definition p130_tri_partial_solve_wit_7 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (((data + ((i - 2 ) * sizeof(INT) ) )) # Int  |-> (Znth ((i - 2 ) - 0 ) (sublist (0) (i) ((tri_sequence (n0)))) 0))
  **  (IntArray.missing_i data (i - 2 ) 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
.

Definition p130_tri_partial_solve_wit_8 := 
forall (n0: Z) (i: Z) (data: Z) (out: Z) ,
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
  **  (IntArray.undef_seg data i (n0 + 1 ) )
|--
  “ ((i % ( 2 ) ) <> 0) ” 
  &&  “ (i <= n0) ” 
  &&  “ (out <> 0) ” 
  &&  “ (data <> 0) ” 
  &&  “ (1 <= n0) ” 
  &&  “ ((n0 + 1 ) < INT_MAX) ” 
  &&  “ (problem_130_pre n0 ) ” 
  &&  “ (tri_seq_int_range n0 ) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n0 + 1 )) ” 
  &&  “ ((Zlength ((tri_sequence (n0)))) = (n0 + 1 )) ”
  &&  (((data + (i * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.undef_seg data (i + 1 ) (n0 + 1 ) )
  **  (IntArray.seg data 0 i (sublist (0) (i) ((tri_sequence (n0)))) )
  **  ((&((out)  # "<anonymous struct>" ->ₛ "data")) # Ptr  |-> data)
  **  ((&((out)  # "<anonymous struct>" ->ₛ "size")) # Int  |-> (n0 + 1 ))
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_p130_tri_safety_wit_1 : p130_tri_safety_wit_1.
Axiom proof_of_p130_tri_safety_wit_2 : p130_tri_safety_wit_2.
Axiom proof_of_p130_tri_safety_wit_3 : p130_tri_safety_wit_3.
Axiom proof_of_p130_tri_safety_wit_4 : p130_tri_safety_wit_4.
Axiom proof_of_p130_tri_safety_wit_5 : p130_tri_safety_wit_5.
Axiom proof_of_p130_tri_safety_wit_6 : p130_tri_safety_wit_6.
Axiom proof_of_p130_tri_safety_wit_7 : p130_tri_safety_wit_7.
Axiom proof_of_p130_tri_safety_wit_8 : p130_tri_safety_wit_8.
Axiom proof_of_p130_tri_safety_wit_9 : p130_tri_safety_wit_9.
Axiom proof_of_p130_tri_safety_wit_10 : p130_tri_safety_wit_10.
Axiom proof_of_p130_tri_safety_wit_11 : p130_tri_safety_wit_11.
Axiom proof_of_p130_tri_safety_wit_12 : p130_tri_safety_wit_12.
Axiom proof_of_p130_tri_safety_wit_13 : p130_tri_safety_wit_13.
Axiom proof_of_p130_tri_safety_wit_14 : p130_tri_safety_wit_14.
Axiom proof_of_p130_tri_safety_wit_15 : p130_tri_safety_wit_15.
Axiom proof_of_p130_tri_safety_wit_16 : p130_tri_safety_wit_16.
Axiom proof_of_p130_tri_safety_wit_17 : p130_tri_safety_wit_17.
Axiom proof_of_p130_tri_safety_wit_18 : p130_tri_safety_wit_18.
Axiom proof_of_p130_tri_safety_wit_19 : p130_tri_safety_wit_19.
Axiom proof_of_p130_tri_safety_wit_20 : p130_tri_safety_wit_20.
Axiom proof_of_p130_tri_safety_wit_21 : p130_tri_safety_wit_21.
Axiom proof_of_p130_tri_safety_wit_22 : p130_tri_safety_wit_22.
Axiom proof_of_p130_tri_safety_wit_23 : p130_tri_safety_wit_23.
Axiom proof_of_p130_tri_safety_wit_24 : p130_tri_safety_wit_24.
Axiom proof_of_p130_tri_safety_wit_25 : p130_tri_safety_wit_25.
Axiom proof_of_p130_tri_safety_wit_26 : p130_tri_safety_wit_26.
Axiom proof_of_p130_tri_safety_wit_27 : p130_tri_safety_wit_27.
Axiom proof_of_p130_tri_safety_wit_28 : p130_tri_safety_wit_28.
Axiom proof_of_p130_tri_safety_wit_29 : p130_tri_safety_wit_29.
Axiom proof_of_p130_tri_safety_wit_30 : p130_tri_safety_wit_30.
Axiom proof_of_p130_tri_safety_wit_31 : p130_tri_safety_wit_31.
Axiom proof_of_p130_tri_entail_wit_1 : p130_tri_entail_wit_1.
Axiom proof_of_p130_tri_entail_wit_2_1 : p130_tri_entail_wit_2_1.
Axiom proof_of_p130_tri_entail_wit_2_2 : p130_tri_entail_wit_2_2.
Axiom proof_of_p130_tri_return_wit_1 : p130_tri_return_wit_1.
Axiom proof_of_p130_tri_return_wit_2 : p130_tri_return_wit_2.
Axiom proof_of_p130_tri_partial_solve_wit_1 : p130_tri_partial_solve_wit_1.
Axiom proof_of_p130_tri_partial_solve_wit_2_pure : p130_tri_partial_solve_wit_2_pure.
Axiom proof_of_p130_tri_partial_solve_wit_2 : p130_tri_partial_solve_wit_2.
Axiom proof_of_p130_tri_partial_solve_wit_3 : p130_tri_partial_solve_wit_3.
Axiom proof_of_p130_tri_partial_solve_wit_4 : p130_tri_partial_solve_wit_4.
Axiom proof_of_p130_tri_partial_solve_wit_5 : p130_tri_partial_solve_wit_5.
Axiom proof_of_p130_tri_partial_solve_wit_6 : p130_tri_partial_solve_wit_6.
Axiom proof_of_p130_tri_partial_solve_wit_7 : p130_tri_partial_solve_wit_7.
Axiom proof_of_p130_tri_partial_solve_wit_8 : p130_tri_partial_solve_wit_8.

End VC_Correct.
