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
Require Import p051_remove_vowels.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p051_remove_vowels -----*)

Definition p051_remove_vowels_safety_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p051_remove_vowels_safety_wit_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p051_remove_vowels_safety_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval_2 (retval + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p051_remove_vowels_safety_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p051_remove_vowels_safety_wit_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition p051_remove_vowels_safety_wit_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition p051_remove_vowels_safety_wit_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition p051_remove_vowels_safety_wit_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition p051_remove_vowels_safety_wit_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition p051_remove_vowels_safety_wit_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p051_remove_vowels_safety_wit_12 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition p051_remove_vowels_safety_wit_13 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition p051_remove_vowels_safety_wit_14 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition p051_remove_vowels_safety_wit_15 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_16 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p051_remove_vowels_safety_wit_17 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full out (j + 1 ) (app (out_l) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> (j + 1 ))
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_18 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_19 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_20 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_21 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_22 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_23 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_24 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_25 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_26 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_27 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p051_remove_vowels_safety_wit_28 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p051_remove_vowels_entail_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval_2 = len) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < len)) -> ((Znth (k_4) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval (retval_2 + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ (out_l = (remove_vowels_prefix (0) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_2 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_6 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_7 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_8 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_9 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_10 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l_2 )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_entail_wit_2_11 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full out (j + 1 ) (app (out_l_2) ((cons ((signed_last_nbits ((Znth i (app (l) ((cons (0) (nil)))) 0)) (8))) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= (i + 1 )) ” 
  &&  “ ((Zlength (out_l)) = (j + 1 )) ” 
  &&  “ (out_l = (remove_vowels_prefix ((i + 1 )) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (j + 1 ))) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (j + 1 ) out_l )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
.

Definition p051_remove_vowels_return_wit_1 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l_2: (@list Z)) (j: Z) (i: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l_2)) = j) ” 
  &&  “ (out_l_2 = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < j)) -> ((Znth (k_4) (out_l_2) (0)) <> 0)) ”
  &&  (CharArray.full out (j + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (j + 1 ) (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_len: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < out_len)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ (0 <= out_len) ” 
  &&  “ (out_len <= len) ” 
  &&  “ ((Zlength (out_l)) = out_len) ” 
  &&  “ (problem_51_spec l out_l ) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (out_len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (len + 1 ) )
.

Definition p051_remove_vowels_partial_solve_wit_1_pure := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p051_remove_vowels_partial_solve_wit_1_aux := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p051_remove_vowels_partial_solve_wit_1 := p051_remove_vowels_partial_solve_wit_1_pure -> p051_remove_vowels_partial_solve_wit_1_aux.

Definition p051_remove_vowels_partial_solve_wit_2_pure := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition p051_remove_vowels_partial_solve_wit_2_aux := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p051_remove_vowels_partial_solve_wit_2 := p051_remove_vowels_partial_solve_wit_2_pure -> p051_remove_vowels_partial_solve_wit_2_aux.

Definition p051_remove_vowels_partial_solve_wit_3 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
.

Definition p051_remove_vowels_partial_solve_wit_4 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out j j (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
.

Definition p051_remove_vowels_partial_solve_wit_5 := 
forall (text_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (out_l: (@list Z)) (j: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
  **  (CharArray.undef_seg out j (len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_51_pre l ) ” 
  &&  “ (char_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ ((Zlength (out_l)) = j) ” 
  &&  “ (out_l = (remove_vowels_prefix (i) (l))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < j)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ”
  &&  (((out + (j * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out j j (len + 1 ) )
  **  (CharArray.full text_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out j out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p051_remove_vowels_safety_wit_1 : p051_remove_vowels_safety_wit_1.
Axiom proof_of_p051_remove_vowels_safety_wit_2 : p051_remove_vowels_safety_wit_2.
Axiom proof_of_p051_remove_vowels_safety_wit_3 : p051_remove_vowels_safety_wit_3.
Axiom proof_of_p051_remove_vowels_safety_wit_4 : p051_remove_vowels_safety_wit_4.
Axiom proof_of_p051_remove_vowels_safety_wit_5 : p051_remove_vowels_safety_wit_5.
Axiom proof_of_p051_remove_vowels_safety_wit_6 : p051_remove_vowels_safety_wit_6.
Axiom proof_of_p051_remove_vowels_safety_wit_7 : p051_remove_vowels_safety_wit_7.
Axiom proof_of_p051_remove_vowels_safety_wit_8 : p051_remove_vowels_safety_wit_8.
Axiom proof_of_p051_remove_vowels_safety_wit_9 : p051_remove_vowels_safety_wit_9.
Axiom proof_of_p051_remove_vowels_safety_wit_10 : p051_remove_vowels_safety_wit_10.
Axiom proof_of_p051_remove_vowels_safety_wit_11 : p051_remove_vowels_safety_wit_11.
Axiom proof_of_p051_remove_vowels_safety_wit_12 : p051_remove_vowels_safety_wit_12.
Axiom proof_of_p051_remove_vowels_safety_wit_13 : p051_remove_vowels_safety_wit_13.
Axiom proof_of_p051_remove_vowels_safety_wit_14 : p051_remove_vowels_safety_wit_14.
Axiom proof_of_p051_remove_vowels_safety_wit_15 : p051_remove_vowels_safety_wit_15.
Axiom proof_of_p051_remove_vowels_safety_wit_16 : p051_remove_vowels_safety_wit_16.
Axiom proof_of_p051_remove_vowels_safety_wit_17 : p051_remove_vowels_safety_wit_17.
Axiom proof_of_p051_remove_vowels_safety_wit_18 : p051_remove_vowels_safety_wit_18.
Axiom proof_of_p051_remove_vowels_safety_wit_19 : p051_remove_vowels_safety_wit_19.
Axiom proof_of_p051_remove_vowels_safety_wit_20 : p051_remove_vowels_safety_wit_20.
Axiom proof_of_p051_remove_vowels_safety_wit_21 : p051_remove_vowels_safety_wit_21.
Axiom proof_of_p051_remove_vowels_safety_wit_22 : p051_remove_vowels_safety_wit_22.
Axiom proof_of_p051_remove_vowels_safety_wit_23 : p051_remove_vowels_safety_wit_23.
Axiom proof_of_p051_remove_vowels_safety_wit_24 : p051_remove_vowels_safety_wit_24.
Axiom proof_of_p051_remove_vowels_safety_wit_25 : p051_remove_vowels_safety_wit_25.
Axiom proof_of_p051_remove_vowels_safety_wit_26 : p051_remove_vowels_safety_wit_26.
Axiom proof_of_p051_remove_vowels_safety_wit_27 : p051_remove_vowels_safety_wit_27.
Axiom proof_of_p051_remove_vowels_safety_wit_28 : p051_remove_vowels_safety_wit_28.
Axiom proof_of_p051_remove_vowels_entail_wit_1 : p051_remove_vowels_entail_wit_1.
Axiom proof_of_p051_remove_vowels_entail_wit_2_1 : p051_remove_vowels_entail_wit_2_1.
Axiom proof_of_p051_remove_vowels_entail_wit_2_2 : p051_remove_vowels_entail_wit_2_2.
Axiom proof_of_p051_remove_vowels_entail_wit_2_3 : p051_remove_vowels_entail_wit_2_3.
Axiom proof_of_p051_remove_vowels_entail_wit_2_4 : p051_remove_vowels_entail_wit_2_4.
Axiom proof_of_p051_remove_vowels_entail_wit_2_5 : p051_remove_vowels_entail_wit_2_5.
Axiom proof_of_p051_remove_vowels_entail_wit_2_6 : p051_remove_vowels_entail_wit_2_6.
Axiom proof_of_p051_remove_vowels_entail_wit_2_7 : p051_remove_vowels_entail_wit_2_7.
Axiom proof_of_p051_remove_vowels_entail_wit_2_8 : p051_remove_vowels_entail_wit_2_8.
Axiom proof_of_p051_remove_vowels_entail_wit_2_9 : p051_remove_vowels_entail_wit_2_9.
Axiom proof_of_p051_remove_vowels_entail_wit_2_10 : p051_remove_vowels_entail_wit_2_10.
Axiom proof_of_p051_remove_vowels_entail_wit_2_11 : p051_remove_vowels_entail_wit_2_11.
Axiom proof_of_p051_remove_vowels_return_wit_1 : p051_remove_vowels_return_wit_1.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_1_pure : p051_remove_vowels_partial_solve_wit_1_pure.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_1 : p051_remove_vowels_partial_solve_wit_1.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_2_pure : p051_remove_vowels_partial_solve_wit_2_pure.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_2 : p051_remove_vowels_partial_solve_wit_2.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_3 : p051_remove_vowels_partial_solve_wit_3.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_4 : p051_remove_vowels_partial_solve_wit_4.
Axiom proof_of_p051_remove_vowels_partial_solve_wit_5 : p051_remove_vowels_partial_solve_wit_5.

End VC_Correct.
