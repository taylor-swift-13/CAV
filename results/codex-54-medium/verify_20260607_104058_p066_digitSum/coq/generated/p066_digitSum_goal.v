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
Require Import p066_digitSum.
Local Open Scope sac.
From output.verify_20260607_104058_p066_digitSum.coq.generated Require Import char_array_strategy_goal.
From output.verify_20260607_104058_p066_digitSum.coq.generated Require Import char_array_strategy_proof.

(*----- Function p066_digitSum -----*)

Definition p066_digitSum_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p066_digitSum_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p066_digitSum_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p066_digitSum_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p066_digitSum_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + (Znth i (app (l) ((cons (0) (nil)))) 0) )) ”
.

Definition p066_digitSum_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p066_digitSum_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p066_digitSum_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "sum" ) )) # Int  |-> (sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p066_digitSum_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = (sum_upper_upto (0) (l))) ” 
  &&  “ (INT_MIN <= 0) ” 
  &&  “ (0 <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_entail_wit_2_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ ((sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ) = (sum_upper_upto ((i + 1 )) (l))) ” 
  &&  “ (INT_MIN <= (sum + (Znth i (app (l) ((cons (0) (nil)))) 0) )) ” 
  &&  “ ((sum + (Znth i (app (l) ((cons (0) (nil)))) 0) ) <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_entail_wit_2_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto ((i + 1 )) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_entail_wit_2_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto ((i + 1 )) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_66_spec l sum ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_partial_solve_wit_1_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p066_digitSum_partial_solve_wit_1_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
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
  &&  “ (problem_66_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_partial_solve_wit_1 := p066_digitSum_partial_solve_wit_1_pure -> p066_digitSum_partial_solve_wit_1_aux.

Definition p066_digitSum_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p066_digitSum_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (digit_sum_int_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (sum = (sum_upper_upto (i) (l))) ” 
  &&  “ (INT_MIN <= sum) ” 
  &&  “ (sum <= INT_MAX) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p066_digitSum_safety_wit_1 : p066_digitSum_safety_wit_1.
Axiom proof_of_p066_digitSum_safety_wit_2 : p066_digitSum_safety_wit_2.
Axiom proof_of_p066_digitSum_safety_wit_3 : p066_digitSum_safety_wit_3.
Axiom proof_of_p066_digitSum_safety_wit_4 : p066_digitSum_safety_wit_4.
Axiom proof_of_p066_digitSum_safety_wit_5 : p066_digitSum_safety_wit_5.
Axiom proof_of_p066_digitSum_safety_wit_6 : p066_digitSum_safety_wit_6.
Axiom proof_of_p066_digitSum_safety_wit_7 : p066_digitSum_safety_wit_7.
Axiom proof_of_p066_digitSum_safety_wit_8 : p066_digitSum_safety_wit_8.
Axiom proof_of_p066_digitSum_entail_wit_1 : p066_digitSum_entail_wit_1.
Axiom proof_of_p066_digitSum_entail_wit_2_1 : p066_digitSum_entail_wit_2_1.
Axiom proof_of_p066_digitSum_entail_wit_2_2 : p066_digitSum_entail_wit_2_2.
Axiom proof_of_p066_digitSum_entail_wit_2_3 : p066_digitSum_entail_wit_2_3.
Axiom proof_of_p066_digitSum_return_wit_1 : p066_digitSum_return_wit_1.
Axiom proof_of_p066_digitSum_partial_solve_wit_1_pure : p066_digitSum_partial_solve_wit_1_pure.
Axiom proof_of_p066_digitSum_partial_solve_wit_1 : p066_digitSum_partial_solve_wit_1.
Axiom proof_of_p066_digitSum_partial_solve_wit_2 : p066_digitSum_partial_solve_wit_2.
Axiom proof_of_p066_digitSum_partial_solve_wit_3 : p066_digitSum_partial_solve_wit_3.
Axiom proof_of_p066_digitSum_partial_solve_wit_4 : p066_digitSum_partial_solve_wit_4.

End VC_Correct.
