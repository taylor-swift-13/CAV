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
Require Import p064_vowels_count.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p064_vowels_count -----*)

Definition p064_vowels_count_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p064_vowels_count_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p064_vowels_count_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition p064_vowels_count_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p064_vowels_count_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (105 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 105) ”
.

Definition p064_vowels_count_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (111 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 111) ”
.

Definition p064_vowels_count_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (117 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 117) ”
.

Definition p064_vowels_count_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p064_vowels_count_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (69 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 69) ”
.

Definition p064_vowels_count_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition p064_vowels_count_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (79 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 79) ”
.

Definition p064_vowels_count_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (85 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 85) ”
.

Definition p064_vowels_count_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_15 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_16 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_17 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_18 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_19 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_20 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_21 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_22 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_23 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_24 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_25 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_26 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_27 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_28 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_29 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_30 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_31 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_32 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_33 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_34 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_35 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_36 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_37 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_38 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_39 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_40 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_41 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_42 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_43 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p064_vowels_count_safety_wit_44 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p064_vowels_count_safety_wit_45 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((len - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 1 )) ”
.

Definition p064_vowels_count_safety_wit_46 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_47 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (121 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 121) ”
.

Definition p064_vowels_count_safety_wit_48 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((len - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 1 )) ”
.

Definition p064_vowels_count_safety_wit_49 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_50 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (89 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 89) ”
.

Definition p064_vowels_count_safety_wit_51 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_52 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_safety_wit_53 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 89) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p064_vowels_count_safety_wit_54 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 89) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p064_vowels_count_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (count_regular_vowels_upto (0) (l))) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_2_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 85) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (count = (count_regular_vowels_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_entail_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_64_spec l (count + 1 ) ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_return_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 89) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_64_spec l (count + 1 ) ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_return_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (len <= 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_64_spec l count ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_return_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 89) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_64_spec l count ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_1_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
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

Definition p064_vowels_count_partial_solve_wit_1_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
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
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_1 := p064_vowels_count_partial_solve_wit_1_pure -> p064_vowels_count_partial_solve_wit_1_aux.

Definition p064_vowels_count_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 79) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 69) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 65) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 117) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 111) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 105) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 97) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (count_regular_vowels_upto (i) (l))) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (((s_pre + ((len - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (len - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p064_vowels_count_partial_solve_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) (count: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 121) ” 
  &&  “ (len > 0) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_64_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= len) ” 
  &&  “ (count = (count_regular_vowels_upto (len) (l))) ”
  &&  (((s_pre + ((len - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (len - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p064_vowels_count_safety_wit_1 : p064_vowels_count_safety_wit_1.
Axiom proof_of_p064_vowels_count_safety_wit_2 : p064_vowels_count_safety_wit_2.
Axiom proof_of_p064_vowels_count_safety_wit_3 : p064_vowels_count_safety_wit_3.
Axiom proof_of_p064_vowels_count_safety_wit_4 : p064_vowels_count_safety_wit_4.
Axiom proof_of_p064_vowels_count_safety_wit_5 : p064_vowels_count_safety_wit_5.
Axiom proof_of_p064_vowels_count_safety_wit_6 : p064_vowels_count_safety_wit_6.
Axiom proof_of_p064_vowels_count_safety_wit_7 : p064_vowels_count_safety_wit_7.
Axiom proof_of_p064_vowels_count_safety_wit_8 : p064_vowels_count_safety_wit_8.
Axiom proof_of_p064_vowels_count_safety_wit_9 : p064_vowels_count_safety_wit_9.
Axiom proof_of_p064_vowels_count_safety_wit_10 : p064_vowels_count_safety_wit_10.
Axiom proof_of_p064_vowels_count_safety_wit_11 : p064_vowels_count_safety_wit_11.
Axiom proof_of_p064_vowels_count_safety_wit_12 : p064_vowels_count_safety_wit_12.
Axiom proof_of_p064_vowels_count_safety_wit_13 : p064_vowels_count_safety_wit_13.
Axiom proof_of_p064_vowels_count_safety_wit_14 : p064_vowels_count_safety_wit_14.
Axiom proof_of_p064_vowels_count_safety_wit_15 : p064_vowels_count_safety_wit_15.
Axiom proof_of_p064_vowels_count_safety_wit_16 : p064_vowels_count_safety_wit_16.
Axiom proof_of_p064_vowels_count_safety_wit_17 : p064_vowels_count_safety_wit_17.
Axiom proof_of_p064_vowels_count_safety_wit_18 : p064_vowels_count_safety_wit_18.
Axiom proof_of_p064_vowels_count_safety_wit_19 : p064_vowels_count_safety_wit_19.
Axiom proof_of_p064_vowels_count_safety_wit_20 : p064_vowels_count_safety_wit_20.
Axiom proof_of_p064_vowels_count_safety_wit_21 : p064_vowels_count_safety_wit_21.
Axiom proof_of_p064_vowels_count_safety_wit_22 : p064_vowels_count_safety_wit_22.
Axiom proof_of_p064_vowels_count_safety_wit_23 : p064_vowels_count_safety_wit_23.
Axiom proof_of_p064_vowels_count_safety_wit_24 : p064_vowels_count_safety_wit_24.
Axiom proof_of_p064_vowels_count_safety_wit_25 : p064_vowels_count_safety_wit_25.
Axiom proof_of_p064_vowels_count_safety_wit_26 : p064_vowels_count_safety_wit_26.
Axiom proof_of_p064_vowels_count_safety_wit_27 : p064_vowels_count_safety_wit_27.
Axiom proof_of_p064_vowels_count_safety_wit_28 : p064_vowels_count_safety_wit_28.
Axiom proof_of_p064_vowels_count_safety_wit_29 : p064_vowels_count_safety_wit_29.
Axiom proof_of_p064_vowels_count_safety_wit_30 : p064_vowels_count_safety_wit_30.
Axiom proof_of_p064_vowels_count_safety_wit_31 : p064_vowels_count_safety_wit_31.
Axiom proof_of_p064_vowels_count_safety_wit_32 : p064_vowels_count_safety_wit_32.
Axiom proof_of_p064_vowels_count_safety_wit_33 : p064_vowels_count_safety_wit_33.
Axiom proof_of_p064_vowels_count_safety_wit_34 : p064_vowels_count_safety_wit_34.
Axiom proof_of_p064_vowels_count_safety_wit_35 : p064_vowels_count_safety_wit_35.
Axiom proof_of_p064_vowels_count_safety_wit_36 : p064_vowels_count_safety_wit_36.
Axiom proof_of_p064_vowels_count_safety_wit_37 : p064_vowels_count_safety_wit_37.
Axiom proof_of_p064_vowels_count_safety_wit_38 : p064_vowels_count_safety_wit_38.
Axiom proof_of_p064_vowels_count_safety_wit_39 : p064_vowels_count_safety_wit_39.
Axiom proof_of_p064_vowels_count_safety_wit_40 : p064_vowels_count_safety_wit_40.
Axiom proof_of_p064_vowels_count_safety_wit_41 : p064_vowels_count_safety_wit_41.
Axiom proof_of_p064_vowels_count_safety_wit_42 : p064_vowels_count_safety_wit_42.
Axiom proof_of_p064_vowels_count_safety_wit_43 : p064_vowels_count_safety_wit_43.
Axiom proof_of_p064_vowels_count_safety_wit_44 : p064_vowels_count_safety_wit_44.
Axiom proof_of_p064_vowels_count_safety_wit_45 : p064_vowels_count_safety_wit_45.
Axiom proof_of_p064_vowels_count_safety_wit_46 : p064_vowels_count_safety_wit_46.
Axiom proof_of_p064_vowels_count_safety_wit_47 : p064_vowels_count_safety_wit_47.
Axiom proof_of_p064_vowels_count_safety_wit_48 : p064_vowels_count_safety_wit_48.
Axiom proof_of_p064_vowels_count_safety_wit_49 : p064_vowels_count_safety_wit_49.
Axiom proof_of_p064_vowels_count_safety_wit_50 : p064_vowels_count_safety_wit_50.
Axiom proof_of_p064_vowels_count_safety_wit_51 : p064_vowels_count_safety_wit_51.
Axiom proof_of_p064_vowels_count_safety_wit_52 : p064_vowels_count_safety_wit_52.
Axiom proof_of_p064_vowels_count_safety_wit_53 : p064_vowels_count_safety_wit_53.
Axiom proof_of_p064_vowels_count_safety_wit_54 : p064_vowels_count_safety_wit_54.
Axiom proof_of_p064_vowels_count_entail_wit_1 : p064_vowels_count_entail_wit_1.
Axiom proof_of_p064_vowels_count_entail_wit_2_1 : p064_vowels_count_entail_wit_2_1.
Axiom proof_of_p064_vowels_count_entail_wit_2_2 : p064_vowels_count_entail_wit_2_2.
Axiom proof_of_p064_vowels_count_entail_wit_2_3 : p064_vowels_count_entail_wit_2_3.
Axiom proof_of_p064_vowels_count_entail_wit_2_4 : p064_vowels_count_entail_wit_2_4.
Axiom proof_of_p064_vowels_count_entail_wit_2_5 : p064_vowels_count_entail_wit_2_5.
Axiom proof_of_p064_vowels_count_entail_wit_2_6 : p064_vowels_count_entail_wit_2_6.
Axiom proof_of_p064_vowels_count_entail_wit_2_7 : p064_vowels_count_entail_wit_2_7.
Axiom proof_of_p064_vowels_count_entail_wit_2_8 : p064_vowels_count_entail_wit_2_8.
Axiom proof_of_p064_vowels_count_entail_wit_2_9 : p064_vowels_count_entail_wit_2_9.
Axiom proof_of_p064_vowels_count_entail_wit_2_10 : p064_vowels_count_entail_wit_2_10.
Axiom proof_of_p064_vowels_count_entail_wit_2_11 : p064_vowels_count_entail_wit_2_11.
Axiom proof_of_p064_vowels_count_entail_wit_3 : p064_vowels_count_entail_wit_3.
Axiom proof_of_p064_vowels_count_return_wit_1 : p064_vowels_count_return_wit_1.
Axiom proof_of_p064_vowels_count_return_wit_2 : p064_vowels_count_return_wit_2.
Axiom proof_of_p064_vowels_count_return_wit_3 : p064_vowels_count_return_wit_3.
Axiom proof_of_p064_vowels_count_return_wit_4 : p064_vowels_count_return_wit_4.
Axiom proof_of_p064_vowels_count_partial_solve_wit_1_pure : p064_vowels_count_partial_solve_wit_1_pure.
Axiom proof_of_p064_vowels_count_partial_solve_wit_1 : p064_vowels_count_partial_solve_wit_1.
Axiom proof_of_p064_vowels_count_partial_solve_wit_2 : p064_vowels_count_partial_solve_wit_2.
Axiom proof_of_p064_vowels_count_partial_solve_wit_3 : p064_vowels_count_partial_solve_wit_3.
Axiom proof_of_p064_vowels_count_partial_solve_wit_4 : p064_vowels_count_partial_solve_wit_4.
Axiom proof_of_p064_vowels_count_partial_solve_wit_5 : p064_vowels_count_partial_solve_wit_5.
Axiom proof_of_p064_vowels_count_partial_solve_wit_6 : p064_vowels_count_partial_solve_wit_6.
Axiom proof_of_p064_vowels_count_partial_solve_wit_7 : p064_vowels_count_partial_solve_wit_7.
Axiom proof_of_p064_vowels_count_partial_solve_wit_8 : p064_vowels_count_partial_solve_wit_8.
Axiom proof_of_p064_vowels_count_partial_solve_wit_9 : p064_vowels_count_partial_solve_wit_9.
Axiom proof_of_p064_vowels_count_partial_solve_wit_10 : p064_vowels_count_partial_solve_wit_10.
Axiom proof_of_p064_vowels_count_partial_solve_wit_11 : p064_vowels_count_partial_solve_wit_11.
Axiom proof_of_p064_vowels_count_partial_solve_wit_12 : p064_vowels_count_partial_solve_wit_12.
Axiom proof_of_p064_vowels_count_partial_solve_wit_13 : p064_vowels_count_partial_solve_wit_13.

End VC_Correct.
