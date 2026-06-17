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
Require Import p027_filp_case.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p027_filp_case -----*)

Definition p027_filp_case_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition p027_filp_case_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p027_filp_case_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p027_filp_case_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition p027_filp_case_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition p027_filp_case_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) ”
.

Definition p027_filp_case_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p027_filp_case_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p027_filp_case_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p027_filp_case_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ False ”
.

Definition p027_filp_case_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p027_filp_case_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p027_filp_case_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ False ”
.

Definition p027_filp_case_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) ”
.

Definition p027_filp_case_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p027_filp_case_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p027_filp_case_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p027_filp_case_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p027_filp_case_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p027_filp_case_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p027_filp_case_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p027_filp_case_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval_2 = len) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < len)) -> ((Znth (k_4) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition p027_filp_case_entail_wit_2_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l_2) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p027_filp_case_entail_wit_2_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l_2) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p027_filp_case_entail_wit_2_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l_2) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p027_filp_case_entail_wit_2_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l_2) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p027_filp_case_entail_wit_2_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l_2) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (((Znth i (app (l) ((cons (0) (nil)))) 0) - 32 )) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (i + 1 ) out_l )
  **  (CharArray.undef_seg out (i + 1 ) (len + 1 ) )
.

Definition p027_filp_case_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (out_l_2) (0)) = (flip_char ((Znth (k_4) (l) (0)))))) ”
  &&  (CharArray.full out (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ ((Zlength (out_l)) = len) ” 
  &&  “ (problem_27_spec l out_l ) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p027_filp_case_partial_solve_wit_1_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
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

Definition p027_filp_case_partial_solve_wit_1_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p027_filp_case_partial_solve_wit_1 := p027_filp_case_partial_solve_wit_1_pure -> p027_filp_case_partial_solve_wit_1_aux.

Definition p027_filp_case_partial_solve_wit_2_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition p027_filp_case_partial_solve_wit_2_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p027_filp_case_partial_solve_wit_2 := p027_filp_case_partial_solve_wit_2_pure -> p027_filp_case_partial_solve_wit_2_aux.

Definition p027_filp_case_partial_solve_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
.

Definition p027_filp_case_partial_solve_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p027_filp_case_partial_solve_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p027_filp_case_partial_solve_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p027_filp_case_partial_solve_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p027_filp_case_partial_solve_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Definition p027_filp_case_partial_solve_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
  **  (CharArray.undef_seg out i (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_27_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (out_l) (0)) = (flip_char ((Znth (k_2) (l) (0)))))) ”
  &&  (((out + (len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out len i (len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p027_filp_case_safety_wit_1 : p027_filp_case_safety_wit_1.
Axiom proof_of_p027_filp_case_safety_wit_2 : p027_filp_case_safety_wit_2.
Axiom proof_of_p027_filp_case_safety_wit_3 : p027_filp_case_safety_wit_3.
Axiom proof_of_p027_filp_case_safety_wit_4 : p027_filp_case_safety_wit_4.
Axiom proof_of_p027_filp_case_safety_wit_5 : p027_filp_case_safety_wit_5.
Axiom proof_of_p027_filp_case_safety_wit_6 : p027_filp_case_safety_wit_6.
Axiom proof_of_p027_filp_case_safety_wit_7 : p027_filp_case_safety_wit_7.
Axiom proof_of_p027_filp_case_safety_wit_8 : p027_filp_case_safety_wit_8.
Axiom proof_of_p027_filp_case_safety_wit_9 : p027_filp_case_safety_wit_9.
Axiom proof_of_p027_filp_case_safety_wit_10 : p027_filp_case_safety_wit_10.
Axiom proof_of_p027_filp_case_safety_wit_11 : p027_filp_case_safety_wit_11.
Axiom proof_of_p027_filp_case_safety_wit_12 : p027_filp_case_safety_wit_12.
Axiom proof_of_p027_filp_case_safety_wit_13 : p027_filp_case_safety_wit_13.
Axiom proof_of_p027_filp_case_safety_wit_14 : p027_filp_case_safety_wit_14.
Axiom proof_of_p027_filp_case_safety_wit_15 : p027_filp_case_safety_wit_15.
Axiom proof_of_p027_filp_case_safety_wit_16 : p027_filp_case_safety_wit_16.
Axiom proof_of_p027_filp_case_safety_wit_17 : p027_filp_case_safety_wit_17.
Axiom proof_of_p027_filp_case_safety_wit_18 : p027_filp_case_safety_wit_18.
Axiom proof_of_p027_filp_case_safety_wit_19 : p027_filp_case_safety_wit_19.
Axiom proof_of_p027_filp_case_safety_wit_20 : p027_filp_case_safety_wit_20.
Axiom proof_of_p027_filp_case_safety_wit_21 : p027_filp_case_safety_wit_21.
Axiom proof_of_p027_filp_case_entail_wit_1 : p027_filp_case_entail_wit_1.
Axiom proof_of_p027_filp_case_entail_wit_2_1 : p027_filp_case_entail_wit_2_1.
Axiom proof_of_p027_filp_case_entail_wit_2_2 : p027_filp_case_entail_wit_2_2.
Axiom proof_of_p027_filp_case_entail_wit_2_3 : p027_filp_case_entail_wit_2_3.
Axiom proof_of_p027_filp_case_entail_wit_2_4 : p027_filp_case_entail_wit_2_4.
Axiom proof_of_p027_filp_case_entail_wit_2_5 : p027_filp_case_entail_wit_2_5.
Axiom proof_of_p027_filp_case_return_wit_1 : p027_filp_case_return_wit_1.
Axiom proof_of_p027_filp_case_partial_solve_wit_1_pure : p027_filp_case_partial_solve_wit_1_pure.
Axiom proof_of_p027_filp_case_partial_solve_wit_1 : p027_filp_case_partial_solve_wit_1.
Axiom proof_of_p027_filp_case_partial_solve_wit_2_pure : p027_filp_case_partial_solve_wit_2_pure.
Axiom proof_of_p027_filp_case_partial_solve_wit_2 : p027_filp_case_partial_solve_wit_2.
Axiom proof_of_p027_filp_case_partial_solve_wit_3 : p027_filp_case_partial_solve_wit_3.
Axiom proof_of_p027_filp_case_partial_solve_wit_4 : p027_filp_case_partial_solve_wit_4.
Axiom proof_of_p027_filp_case_partial_solve_wit_5 : p027_filp_case_partial_solve_wit_5.
Axiom proof_of_p027_filp_case_partial_solve_wit_6 : p027_filp_case_partial_solve_wit_6.
Axiom proof_of_p027_filp_case_partial_solve_wit_7 : p027_filp_case_partial_solve_wit_7.
Axiom proof_of_p027_filp_case_partial_solve_wit_8 : p027_filp_case_partial_solve_wit_8.
Axiom proof_of_p027_filp_case_partial_solve_wit_9 : p027_filp_case_partial_solve_wit_9.

End VC_Correct.
