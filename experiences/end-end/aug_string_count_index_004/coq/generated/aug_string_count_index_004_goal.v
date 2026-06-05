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
Require Import aug_string_count_index_004.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function aug_string_count_index_004 -----*)

Definition aug_string_count_index_004_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition aug_string_count_index_004_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition aug_string_count_index_004_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition aug_string_count_index_004_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition aug_string_count_index_004_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition aug_string_count_index_004_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition aug_string_count_index_004_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition aug_string_count_index_004_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition aug_string_count_index_004_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = 0) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1_2) (l2_2))) ” 
  &&  “ ((Zlength (l1_2)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1_2))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = (i + 1 )) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ ((count + 1 ) = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1_2) (l2_2))) ” 
  &&  “ ((Zlength (l1_2)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1_2))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = (i + 1 )) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1_2: (@list Z)) (l2_2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1_2) (l2_2))) ” 
  &&  “ ((Zlength (l1_2)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1_2))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth k_3 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (0 <= count) ” 
  &&  “ (count <= n) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) ,
  “ (0 <= count) ” 
  &&  “ (count <= n) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = n) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (count = (aug_string_count_index_004_spec (l))) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition aug_string_count_index_004_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (l1: (@list Z)) (l2: (@list Z)) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ ((Zlength (l1)) = i) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (count = (aug_string_count_index_004_spec (l1))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_aug_string_count_index_004_safety_wit_1 : aug_string_count_index_004_safety_wit_1.
Axiom proof_of_aug_string_count_index_004_safety_wit_2 : aug_string_count_index_004_safety_wit_2.
Axiom proof_of_aug_string_count_index_004_safety_wit_3 : aug_string_count_index_004_safety_wit_3.
Axiom proof_of_aug_string_count_index_004_safety_wit_4 : aug_string_count_index_004_safety_wit_4.
Axiom proof_of_aug_string_count_index_004_safety_wit_5 : aug_string_count_index_004_safety_wit_5.
Axiom proof_of_aug_string_count_index_004_safety_wit_6 : aug_string_count_index_004_safety_wit_6.
Axiom proof_of_aug_string_count_index_004_safety_wit_7 : aug_string_count_index_004_safety_wit_7.
Axiom proof_of_aug_string_count_index_004_safety_wit_8 : aug_string_count_index_004_safety_wit_8.
Axiom proof_of_aug_string_count_index_004_entail_wit_1 : aug_string_count_index_004_entail_wit_1.
Axiom proof_of_aug_string_count_index_004_entail_wit_2_1 : aug_string_count_index_004_entail_wit_2_1.
Axiom proof_of_aug_string_count_index_004_entail_wit_2_2 : aug_string_count_index_004_entail_wit_2_2.
Axiom proof_of_aug_string_count_index_004_entail_wit_3 : aug_string_count_index_004_entail_wit_3.
Axiom proof_of_aug_string_count_index_004_return_wit_1 : aug_string_count_index_004_return_wit_1.
Axiom proof_of_aug_string_count_index_004_partial_solve_wit_1 : aug_string_count_index_004_partial_solve_wit_1.
Axiom proof_of_aug_string_count_index_004_partial_solve_wit_2 : aug_string_count_index_004_partial_solve_wit_2.

End VC_Correct.
