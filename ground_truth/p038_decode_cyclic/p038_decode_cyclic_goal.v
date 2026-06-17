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
Require Import p038_decode_cyclic.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p038_decode_cyclic -----*)

Definition p038_decode_cyclic_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p038_decode_cyclic_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "full" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (((retval ÷ 3 ) * 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((retval ÷ 3 ) * 3 )) ”
.

Definition p038_decode_cyclic_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "full" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition p038_decode_cyclic_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "full" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p038_decode_cyclic_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "full" ) )) # Int  |->_)
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p038_decode_cyclic_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "full" ) )) # Int  |-> ((retval ÷ 3 ) * 3 ))
  **  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p038_decode_cyclic_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (((i + 1 ) <> (INT_MIN)) \/ (3 <> (-1))) ” 
  &&  “ (3 <> 0) ”
.

Definition p038_decode_cyclic_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p038_decode_cyclic_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p038_decode_cyclic_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p038_decode_cyclic_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ ((i + 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 2 )) ”
.

Definition p038_decode_cyclic_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p038_decode_cyclic_safety_wit_15 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_16 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p038_decode_cyclic_safety_wit_17 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_18 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_19 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth (i + 2 ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p038_decode_cyclic_safety_wit_20 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i >= len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "full" ) )) # Int  |-> full)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p038_decode_cyclic_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < len)) -> ((Znth (k_4) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  EX (out_l: (@list Z)) ,
  “ (((retval ÷ 3 ) * 3 ) = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval_2 0 out_l )
  **  (CharArray.undef_seg retval_2 0 (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (full: Z) ,
  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (full: Z) ,
  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (i < full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (full: Z) ,
  “ (i >= full) ” 
  &&  “ (i < len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l_2 )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_5_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth (i + 2 ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_5_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p038_decode_cyclic_entail_wit_5_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l_2: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p038_decode_cyclic_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) (full: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (decode_char (len) (l) (k_4)))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ ((Zlength (out_l)) = len) ” 
  &&  “ (problem_38_spec l out_l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p038_decode_cyclic_partial_solve_wit_1_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p038_decode_cyclic_partial_solve_wit_1_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p038_decode_cyclic_partial_solve_wit_1 := p038_decode_cyclic_partial_solve_wit_1_pure -> p038_decode_cyclic_partial_solve_wit_1_aux.

Definition p038_decode_cyclic_partial_solve_wit_2_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition p038_decode_cyclic_partial_solve_wit_2_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p038_decode_cyclic_partial_solve_wit_2 := p038_decode_cyclic_partial_solve_wit_2_pure -> p038_decode_cyclic_partial_solve_wit_2_aux.

Definition p038_decode_cyclic_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (((s_pre + ((i + 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i + 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i + 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) = 1) ” 
  &&  “ (0 <= (i + 2 )) ” 
  &&  “ ((i + 2 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i + 2 )) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p038_decode_cyclic_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (((s_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i < full) ” 
  &&  “ (((i + 1 ) % ( 3 ) ) <> 1) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) < len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = (i - 1 )) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p038_decode_cyclic_partial_solve_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p038_decode_cyclic_partial_solve_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out_l: (@list Z)) (full: Z) (i: Z) (out: Z) ,
  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < len) ” 
  &&  “ (i >= full) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ” 
  &&  “ ((decode_source_index (len) (i)) = i) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p038_decode_cyclic_partial_solve_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) (full: Z) ,
  “ (i >= len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ (full = (full_decode_len (len))) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_38_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (decode_char (len) (l) (k_2)))) ”
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p038_decode_cyclic_safety_wit_1 : p038_decode_cyclic_safety_wit_1.
Axiom proof_of_p038_decode_cyclic_safety_wit_2 : p038_decode_cyclic_safety_wit_2.
Axiom proof_of_p038_decode_cyclic_safety_wit_3 : p038_decode_cyclic_safety_wit_3.
Axiom proof_of_p038_decode_cyclic_safety_wit_4 : p038_decode_cyclic_safety_wit_4.
Axiom proof_of_p038_decode_cyclic_safety_wit_5 : p038_decode_cyclic_safety_wit_5.
Axiom proof_of_p038_decode_cyclic_safety_wit_6 : p038_decode_cyclic_safety_wit_6.
Axiom proof_of_p038_decode_cyclic_safety_wit_7 : p038_decode_cyclic_safety_wit_7.
Axiom proof_of_p038_decode_cyclic_safety_wit_8 : p038_decode_cyclic_safety_wit_8.
Axiom proof_of_p038_decode_cyclic_safety_wit_9 : p038_decode_cyclic_safety_wit_9.
Axiom proof_of_p038_decode_cyclic_safety_wit_10 : p038_decode_cyclic_safety_wit_10.
Axiom proof_of_p038_decode_cyclic_safety_wit_11 : p038_decode_cyclic_safety_wit_11.
Axiom proof_of_p038_decode_cyclic_safety_wit_12 : p038_decode_cyclic_safety_wit_12.
Axiom proof_of_p038_decode_cyclic_safety_wit_13 : p038_decode_cyclic_safety_wit_13.
Axiom proof_of_p038_decode_cyclic_safety_wit_14 : p038_decode_cyclic_safety_wit_14.
Axiom proof_of_p038_decode_cyclic_safety_wit_15 : p038_decode_cyclic_safety_wit_15.
Axiom proof_of_p038_decode_cyclic_safety_wit_16 : p038_decode_cyclic_safety_wit_16.
Axiom proof_of_p038_decode_cyclic_safety_wit_17 : p038_decode_cyclic_safety_wit_17.
Axiom proof_of_p038_decode_cyclic_safety_wit_18 : p038_decode_cyclic_safety_wit_18.
Axiom proof_of_p038_decode_cyclic_safety_wit_19 : p038_decode_cyclic_safety_wit_19.
Axiom proof_of_p038_decode_cyclic_safety_wit_20 : p038_decode_cyclic_safety_wit_20.
Axiom proof_of_p038_decode_cyclic_entail_wit_1 : p038_decode_cyclic_entail_wit_1.
Axiom proof_of_p038_decode_cyclic_entail_wit_2 : p038_decode_cyclic_entail_wit_2.
Axiom proof_of_p038_decode_cyclic_entail_wit_3 : p038_decode_cyclic_entail_wit_3.
Axiom proof_of_p038_decode_cyclic_entail_wit_4 : p038_decode_cyclic_entail_wit_4.
Axiom proof_of_p038_decode_cyclic_entail_wit_5_1 : p038_decode_cyclic_entail_wit_5_1.
Axiom proof_of_p038_decode_cyclic_entail_wit_5_2 : p038_decode_cyclic_entail_wit_5_2.
Axiom proof_of_p038_decode_cyclic_entail_wit_5_3 : p038_decode_cyclic_entail_wit_5_3.
Axiom proof_of_p038_decode_cyclic_return_wit_1 : p038_decode_cyclic_return_wit_1.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_1_pure : p038_decode_cyclic_partial_solve_wit_1_pure.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_1 : p038_decode_cyclic_partial_solve_wit_1.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_2_pure : p038_decode_cyclic_partial_solve_wit_2_pure.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_2 : p038_decode_cyclic_partial_solve_wit_2.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_3 : p038_decode_cyclic_partial_solve_wit_3.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_4 : p038_decode_cyclic_partial_solve_wit_4.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_5 : p038_decode_cyclic_partial_solve_wit_5.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_6 : p038_decode_cyclic_partial_solve_wit_6.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_7 : p038_decode_cyclic_partial_solve_wit_7.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_8 : p038_decode_cyclic_partial_solve_wit_8.
Axiom proof_of_p038_decode_cyclic_partial_solve_wit_9 : p038_decode_cyclic_partial_solve_wit_9.

End VC_Correct.
