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
Require Import string_bridge.
Require Import p118_get_closest_vowel.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function is_vowel_code -----*)

Definition is_vowel_code_safety_wit_1 := 
forall (ch_pre: Z) ,
  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition is_vowel_code_safety_wit_2 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_3 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition is_vowel_code_safety_wit_4 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_5 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition is_vowel_code_safety_wit_6 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_7 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition is_vowel_code_safety_wit_8 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_9 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition is_vowel_code_safety_wit_10 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_11 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition is_vowel_code_safety_wit_12 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_13 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition is_vowel_code_safety_wit_14 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_15 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition is_vowel_code_safety_wit_16 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_17 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition is_vowel_code_safety_wit_18 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_19 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition is_vowel_code_safety_wit_20 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 117) ” 
  &&  “ (ch_pre <> 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_vowel_code_safety_wit_21 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 117) ” 
  &&  “ (ch_pre <> 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  ((( &( "ch" ) )) # Int  |-> ch_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_vowel_code_return_wit_1 := 
forall (ch_pre: Z) ,
  “ (ch_pre <> 117) ” 
  &&  “ (ch_pre <> 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (0 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (0 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_2 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 117) ” 
  &&  “ (ch_pre <> 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_3 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 111) ” 
  &&  “ (ch_pre <> 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_4 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 105) ” 
  &&  “ (ch_pre <> 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_5 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 101) ” 
  &&  “ (ch_pre <> 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_6 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 97) ” 
  &&  “ (ch_pre <> 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_7 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 85) ” 
  &&  “ (ch_pre <> 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_8 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 79) ” 
  &&  “ (ch_pre <> 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_9 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 73) ” 
  &&  “ (ch_pre <> 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_10 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 69) ” 
  &&  “ (ch_pre <> 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

Definition is_vowel_code_return_wit_11 := 
forall (ch_pre: Z) ,
  “ (ch_pre = 65) ”
  &&  emp
|--
  (“ (1 = 0) ” 
  &&  “ ~((is_vowel ch_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ” 
  &&  “ (is_vowel ch_pre ) ”
  &&  emp)
.

(*----- Function p118_get_closest_vowel -----*)

Definition p118_get_closest_vowel_safety_wit_1 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_2 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_3 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_4 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_5 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_6 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_7 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p118_get_closest_vowel_safety_wit_8 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_9 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full retval_2 0 nil )
  **  (CharArray.undef_seg retval_2 0 1 )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_10 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full retval_2 0 nil )
  **  (CharArray.undef_seg retval_2 0 1 )
  **  ((( &( "out" ) )) # Ptr  |-> retval_2)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_11 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ ((retval - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 2 )) ”
.

Definition p118_get_closest_vowel_safety_wit_12 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p118_get_closest_vowel_safety_wit_13 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) (cur: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_14 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p118_get_closest_vowel_safety_wit_15 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) (right: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_16 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition p118_get_closest_vowel_safety_wit_17 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (cur_vowel: Z) (left: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_18 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_19 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_20 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_21 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (right_vowel: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_22 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 1) ” 
  &&  “ (is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_23 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_24 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_25 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (left_vowel: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_26 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = 1) ” 
  &&  “ (is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_27 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ ~((is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_28 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_29 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ~((is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "right" ) )) # Int  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "left" ) )) # Int  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "cur_vowel" ) )) # Int  |-> retval)
  **  ((( &( "right_vowel" ) )) # Int  |-> retval_2)
  **  ((( &( "left_vowel" ) )) # Int  |-> retval_3)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ False ”
.

Definition p118_get_closest_vowel_safety_wit_30 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p118_get_closest_vowel_safety_wit_31 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval 0 nil )
  **  (CharArray.undef_seg retval 0 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_32 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) ,
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval (0 + 1 ) (app (nil) ((cons ((signed_last_nbits (cur) (8))) (nil)))) )
  **  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_33 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) ,
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval (0 + 1 ) (app (nil) ((cons ((signed_last_nbits (cur) (8))) (nil)))) )
  **  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_34 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition p118_get_closest_vowel_safety_wit_35 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_36 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p118_get_closest_vowel_safety_wit_37 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full retval 0 nil )
  **  (CharArray.undef_seg retval 0 1 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_safety_wit_38 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full retval 0 nil )
  **  (CharArray.undef_seg retval 0 1 )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p118_get_closest_vowel_entail_wit_1 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= (retval - 2 )) ” 
  &&  “ ((retval - 2 ) <= (len - 2 )) ” 
  &&  “ (no_candidate_after (retval - 2 ) l ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_2 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 = 0) ” 
  &&  “ (retval_3 = 0) ” 
  &&  “ ~((is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i) (l) (0))) ” 
  &&  “ ((Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ ((Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_3_1 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) (retval_3: Z) ,
  “ (retval_3 <> 0) ” 
  &&  “ (retval_3 = 1) ” 
  &&  “ (is_vowel (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_3_2 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = 1) ” 
  &&  “ (is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_3_3 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_4 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ ~((closest_vowel_candidate l i )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= (len - 2 )) ” 
  &&  “ (no_candidate_after (i - 1 ) l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_entail_wit_5 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i < 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_return_wit_1 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) ,
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full retval (0 + 1 ) (app (nil) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg retval (0 + 1 ) 1 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < out_n)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ ((Zlength (out_l)) = out_n) ” 
  &&  “ (0 <= out_n) ” 
  &&  “ (out_n <= 1) ” 
  &&  “ (problem_118_spec l out_l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval (out_n + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_return_wit_2 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (i: Z) (retval: Z) ,
  “ (0 <= (0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval ((0 + 1 ) + 1 ) (app ((app (nil) ((cons ((signed_last_nbits (cur) (8))) (nil))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < out_n)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ ((Zlength (out_l)) = out_n) ” 
  &&  “ (0 <= out_n) ” 
  &&  “ (out_n <= 1) ” 
  &&  “ (problem_118_spec l out_l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval (out_n + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_return_wit_3 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval_2 < 3) ” 
  &&  “ (retval_2 = len) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < len)) -> ((Znth (k_4) (l) (0)) <> 0)) ”
  &&  (CharArray.full retval (0 + 1 ) (app (nil) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg retval (0 + 1 ) 1 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (out_n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < out_n)) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ ((Zlength (out_l)) = out_n) ” 
  &&  “ (0 <= out_n) ” 
  &&  “ (out_n <= 1) ” 
  &&  “ (problem_118_spec l out_l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full retval (out_n + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_1_pure := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "left_vowel" ) )) # Int  |->_)
  **  ((( &( "right_vowel" ) )) # Int  |->_)
  **  ((( &( "cur_vowel" ) )) # Int  |->_)
  **  ((( &( "left" ) )) # Int  |->_)
  **  ((( &( "right" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p118_get_closest_vowel_partial_solve_wit_1_aux := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_1 := p118_get_closest_vowel_partial_solve_wit_1_pure -> p118_get_closest_vowel_partial_solve_wit_1_aux.

Definition p118_get_closest_vowel_partial_solve_wit_2_pure := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "left_vowel" ) )) # Int  |-> 0)
  **  ((( &( "right_vowel" ) )) # Int  |-> 0)
  **  ((( &( "cur_vowel" ) )) # Int  |-> 0)
  **  ((( &( "left" ) )) # Int  |-> 0)
  **  ((( &( "right" ) )) # Int  |-> 0)
  **  ((( &( "cur" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
|--
  “ (1 > 0) ”
.

Definition p118_get_closest_vowel_partial_solve_wit_2_aux := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_2 := p118_get_closest_vowel_partial_solve_wit_2_pure -> p118_get_closest_vowel_partial_solve_wit_2_aux.

Definition p118_get_closest_vowel_partial_solve_wit_3 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full retval_2 0 nil )
  **  (CharArray.undef_seg retval_2 0 1 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((retval_2 + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval_2 0 0 1 )
  **  (CharArray.full retval_2 0 nil )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_4 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (((word_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i word_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_5 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (((word_pre + ((i + 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i word_pre (i + 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_6 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (((word_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i word_pre (i - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_7 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_8 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_9 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = 0) ” 
  &&  “ ~((is_vowel (Znth (i + 1 ) (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ (retval = 1) ” 
  &&  “ (retval = 1) ” 
  &&  “ (is_vowel (Znth i (app (l) ((cons (0) (nil)))) 0) ) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (i >= 1) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_10_pure := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (2 > 0) ”
.

Definition p118_get_closest_vowel_partial_solve_wit_10_aux := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (2 > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_10 := p118_get_closest_vowel_partial_solve_wit_10_pure -> p118_get_closest_vowel_partial_solve_wit_10_aux.

Definition p118_get_closest_vowel_partial_solve_wit_11 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval 0 nil )
  **  (CharArray.undef_seg retval 0 2 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
  **  (CharArray.full retval 0 nil )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_12 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (i: Z) (retval: Z) ,
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (CharArray.full retval (0 + 1 ) (app (nil) ((cons ((signed_last_nbits (cur) (8))) (nil)))) )
  **  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (0 + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (len - 2 )) ” 
  &&  “ (cur = (Znth (i) (l) (0))) ” 
  &&  “ (right = (Znth ((i + 1 )) (l) (0))) ” 
  &&  “ (left = (Znth ((i - 1 )) (l) (0))) ” 
  &&  “ (closest_vowel_candidate l i ) ” 
  &&  “ (no_candidate_after i l ) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (CharArray.full retval (0 + 1 ) (app (nil) ((cons ((signed_last_nbits (cur) (8))) (nil)))) )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_13_pure := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (cur: Z) (right: Z) (left: Z) (cur_vowel: Z) (right_vowel: Z) (left_vowel: Z) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "word" ) )) # Ptr  |-> word_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "right" ) )) # Int  |-> right)
  **  ((( &( "left" ) )) # Int  |-> left)
  **  ((( &( "cur_vowel" ) )) # Int  |-> cur_vowel)
  **  ((( &( "right_vowel" ) )) # Int  |-> right_vowel)
  **  ((( &( "left_vowel" ) )) # Int  |-> left_vowel)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 > 0) ”
.

Definition p118_get_closest_vowel_partial_solve_wit_13_aux := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p118_get_closest_vowel_partial_solve_wit_13 := p118_get_closest_vowel_partial_solve_wit_13_pure -> p118_get_closest_vowel_partial_solve_wit_13_aux.

Definition p118_get_closest_vowel_partial_solve_wit_14 := 
forall (word_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (CharArray.full retval 0 nil )
  **  (CharArray.undef_seg retval 0 1 )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_118_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (alpha_range l ) ” 
  &&  “ (i = 0) ” 
  &&  “ (no_candidate_after 0 l ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 1 )
  **  (CharArray.full retval 0 nil )
  **  (CharArray.full word_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_vowel_code_safety_wit_1 : is_vowel_code_safety_wit_1.
Axiom proof_of_is_vowel_code_safety_wit_2 : is_vowel_code_safety_wit_2.
Axiom proof_of_is_vowel_code_safety_wit_3 : is_vowel_code_safety_wit_3.
Axiom proof_of_is_vowel_code_safety_wit_4 : is_vowel_code_safety_wit_4.
Axiom proof_of_is_vowel_code_safety_wit_5 : is_vowel_code_safety_wit_5.
Axiom proof_of_is_vowel_code_safety_wit_6 : is_vowel_code_safety_wit_6.
Axiom proof_of_is_vowel_code_safety_wit_7 : is_vowel_code_safety_wit_7.
Axiom proof_of_is_vowel_code_safety_wit_8 : is_vowel_code_safety_wit_8.
Axiom proof_of_is_vowel_code_safety_wit_9 : is_vowel_code_safety_wit_9.
Axiom proof_of_is_vowel_code_safety_wit_10 : is_vowel_code_safety_wit_10.
Axiom proof_of_is_vowel_code_safety_wit_11 : is_vowel_code_safety_wit_11.
Axiom proof_of_is_vowel_code_safety_wit_12 : is_vowel_code_safety_wit_12.
Axiom proof_of_is_vowel_code_safety_wit_13 : is_vowel_code_safety_wit_13.
Axiom proof_of_is_vowel_code_safety_wit_14 : is_vowel_code_safety_wit_14.
Axiom proof_of_is_vowel_code_safety_wit_15 : is_vowel_code_safety_wit_15.
Axiom proof_of_is_vowel_code_safety_wit_16 : is_vowel_code_safety_wit_16.
Axiom proof_of_is_vowel_code_safety_wit_17 : is_vowel_code_safety_wit_17.
Axiom proof_of_is_vowel_code_safety_wit_18 : is_vowel_code_safety_wit_18.
Axiom proof_of_is_vowel_code_safety_wit_19 : is_vowel_code_safety_wit_19.
Axiom proof_of_is_vowel_code_safety_wit_20 : is_vowel_code_safety_wit_20.
Axiom proof_of_is_vowel_code_safety_wit_21 : is_vowel_code_safety_wit_21.
Axiom proof_of_is_vowel_code_return_wit_1 : is_vowel_code_return_wit_1.
Axiom proof_of_is_vowel_code_return_wit_2 : is_vowel_code_return_wit_2.
Axiom proof_of_is_vowel_code_return_wit_3 : is_vowel_code_return_wit_3.
Axiom proof_of_is_vowel_code_return_wit_4 : is_vowel_code_return_wit_4.
Axiom proof_of_is_vowel_code_return_wit_5 : is_vowel_code_return_wit_5.
Axiom proof_of_is_vowel_code_return_wit_6 : is_vowel_code_return_wit_6.
Axiom proof_of_is_vowel_code_return_wit_7 : is_vowel_code_return_wit_7.
Axiom proof_of_is_vowel_code_return_wit_8 : is_vowel_code_return_wit_8.
Axiom proof_of_is_vowel_code_return_wit_9 : is_vowel_code_return_wit_9.
Axiom proof_of_is_vowel_code_return_wit_10 : is_vowel_code_return_wit_10.
Axiom proof_of_is_vowel_code_return_wit_11 : is_vowel_code_return_wit_11.
Axiom proof_of_p118_get_closest_vowel_safety_wit_1 : p118_get_closest_vowel_safety_wit_1.
Axiom proof_of_p118_get_closest_vowel_safety_wit_2 : p118_get_closest_vowel_safety_wit_2.
Axiom proof_of_p118_get_closest_vowel_safety_wit_3 : p118_get_closest_vowel_safety_wit_3.
Axiom proof_of_p118_get_closest_vowel_safety_wit_4 : p118_get_closest_vowel_safety_wit_4.
Axiom proof_of_p118_get_closest_vowel_safety_wit_5 : p118_get_closest_vowel_safety_wit_5.
Axiom proof_of_p118_get_closest_vowel_safety_wit_6 : p118_get_closest_vowel_safety_wit_6.
Axiom proof_of_p118_get_closest_vowel_safety_wit_7 : p118_get_closest_vowel_safety_wit_7.
Axiom proof_of_p118_get_closest_vowel_safety_wit_8 : p118_get_closest_vowel_safety_wit_8.
Axiom proof_of_p118_get_closest_vowel_safety_wit_9 : p118_get_closest_vowel_safety_wit_9.
Axiom proof_of_p118_get_closest_vowel_safety_wit_10 : p118_get_closest_vowel_safety_wit_10.
Axiom proof_of_p118_get_closest_vowel_safety_wit_11 : p118_get_closest_vowel_safety_wit_11.
Axiom proof_of_p118_get_closest_vowel_safety_wit_12 : p118_get_closest_vowel_safety_wit_12.
Axiom proof_of_p118_get_closest_vowel_safety_wit_13 : p118_get_closest_vowel_safety_wit_13.
Axiom proof_of_p118_get_closest_vowel_safety_wit_14 : p118_get_closest_vowel_safety_wit_14.
Axiom proof_of_p118_get_closest_vowel_safety_wit_15 : p118_get_closest_vowel_safety_wit_15.
Axiom proof_of_p118_get_closest_vowel_safety_wit_16 : p118_get_closest_vowel_safety_wit_16.
Axiom proof_of_p118_get_closest_vowel_safety_wit_17 : p118_get_closest_vowel_safety_wit_17.
Axiom proof_of_p118_get_closest_vowel_safety_wit_18 : p118_get_closest_vowel_safety_wit_18.
Axiom proof_of_p118_get_closest_vowel_safety_wit_19 : p118_get_closest_vowel_safety_wit_19.
Axiom proof_of_p118_get_closest_vowel_safety_wit_20 : p118_get_closest_vowel_safety_wit_20.
Axiom proof_of_p118_get_closest_vowel_safety_wit_21 : p118_get_closest_vowel_safety_wit_21.
Axiom proof_of_p118_get_closest_vowel_safety_wit_22 : p118_get_closest_vowel_safety_wit_22.
Axiom proof_of_p118_get_closest_vowel_safety_wit_23 : p118_get_closest_vowel_safety_wit_23.
Axiom proof_of_p118_get_closest_vowel_safety_wit_24 : p118_get_closest_vowel_safety_wit_24.
Axiom proof_of_p118_get_closest_vowel_safety_wit_25 : p118_get_closest_vowel_safety_wit_25.
Axiom proof_of_p118_get_closest_vowel_safety_wit_26 : p118_get_closest_vowel_safety_wit_26.
Axiom proof_of_p118_get_closest_vowel_safety_wit_27 : p118_get_closest_vowel_safety_wit_27.
Axiom proof_of_p118_get_closest_vowel_safety_wit_28 : p118_get_closest_vowel_safety_wit_28.
Axiom proof_of_p118_get_closest_vowel_safety_wit_29 : p118_get_closest_vowel_safety_wit_29.
Axiom proof_of_p118_get_closest_vowel_safety_wit_30 : p118_get_closest_vowel_safety_wit_30.
Axiom proof_of_p118_get_closest_vowel_safety_wit_31 : p118_get_closest_vowel_safety_wit_31.
Axiom proof_of_p118_get_closest_vowel_safety_wit_32 : p118_get_closest_vowel_safety_wit_32.
Axiom proof_of_p118_get_closest_vowel_safety_wit_33 : p118_get_closest_vowel_safety_wit_33.
Axiom proof_of_p118_get_closest_vowel_safety_wit_34 : p118_get_closest_vowel_safety_wit_34.
Axiom proof_of_p118_get_closest_vowel_safety_wit_35 : p118_get_closest_vowel_safety_wit_35.
Axiom proof_of_p118_get_closest_vowel_safety_wit_36 : p118_get_closest_vowel_safety_wit_36.
Axiom proof_of_p118_get_closest_vowel_safety_wit_37 : p118_get_closest_vowel_safety_wit_37.
Axiom proof_of_p118_get_closest_vowel_safety_wit_38 : p118_get_closest_vowel_safety_wit_38.
Axiom proof_of_p118_get_closest_vowel_entail_wit_1 : p118_get_closest_vowel_entail_wit_1.
Axiom proof_of_p118_get_closest_vowel_entail_wit_2 : p118_get_closest_vowel_entail_wit_2.
Axiom proof_of_p118_get_closest_vowel_entail_wit_3_1 : p118_get_closest_vowel_entail_wit_3_1.
Axiom proof_of_p118_get_closest_vowel_entail_wit_3_2 : p118_get_closest_vowel_entail_wit_3_2.
Axiom proof_of_p118_get_closest_vowel_entail_wit_3_3 : p118_get_closest_vowel_entail_wit_3_3.
Axiom proof_of_p118_get_closest_vowel_entail_wit_4 : p118_get_closest_vowel_entail_wit_4.
Axiom proof_of_p118_get_closest_vowel_entail_wit_5 : p118_get_closest_vowel_entail_wit_5.
Axiom proof_of_p118_get_closest_vowel_return_wit_1 : p118_get_closest_vowel_return_wit_1.
Axiom proof_of_p118_get_closest_vowel_return_wit_2 : p118_get_closest_vowel_return_wit_2.
Axiom proof_of_p118_get_closest_vowel_return_wit_3 : p118_get_closest_vowel_return_wit_3.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_1_pure : p118_get_closest_vowel_partial_solve_wit_1_pure.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_1 : p118_get_closest_vowel_partial_solve_wit_1.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_2_pure : p118_get_closest_vowel_partial_solve_wit_2_pure.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_2 : p118_get_closest_vowel_partial_solve_wit_2.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_3 : p118_get_closest_vowel_partial_solve_wit_3.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_4 : p118_get_closest_vowel_partial_solve_wit_4.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_5 : p118_get_closest_vowel_partial_solve_wit_5.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_6 : p118_get_closest_vowel_partial_solve_wit_6.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_7 : p118_get_closest_vowel_partial_solve_wit_7.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_8 : p118_get_closest_vowel_partial_solve_wit_8.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_9 : p118_get_closest_vowel_partial_solve_wit_9.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_10_pure : p118_get_closest_vowel_partial_solve_wit_10_pure.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_10 : p118_get_closest_vowel_partial_solve_wit_10.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_11 : p118_get_closest_vowel_partial_solve_wit_11.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_12 : p118_get_closest_vowel_partial_solve_wit_12.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_13_pure : p118_get_closest_vowel_partial_solve_wit_13_pure.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_13 : p118_get_closest_vowel_partial_solve_wit_13.
Axiom proof_of_p118_get_closest_vowel_partial_solve_wit_14 : p118_get_closest_vowel_partial_solve_wit_14.

End VC_Correct.
