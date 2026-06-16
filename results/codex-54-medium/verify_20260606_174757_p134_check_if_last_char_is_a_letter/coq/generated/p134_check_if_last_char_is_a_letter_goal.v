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
Require Import p134_check_if_last_char_is_a_letter.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p134_check_if_last_char_is_a_letter -----*)

Definition p134_check_if_last_char_is_a_letter_safety_wit_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "chr" ) )) # Int  |->_)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_4 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "chr" ) )) # Int  |->_)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_5 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_6 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_7 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_8 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_9 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_10 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_11 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_12 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ False ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_13 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_14 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_15 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_16 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_17 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_18 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ ((retval - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 2 )) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_19 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_20 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ ((retval - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 2 )) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_21 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_22 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_23 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_24 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_25 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_26 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_safety_wit_27 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p134_check_if_last_char_is_a_letter_return_wit_1 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 1 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_4 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 1 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_5 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 1 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_6 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 1 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_7 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_8 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_9 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_return_wit_10 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_134_spec l 0 ) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_1_pure := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "txt" ) )) # Ptr  |-> txt_pre)
  **  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_1_aux := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_1 := p134_check_if_last_char_is_a_letter_partial_solve_wit_1_pure -> p134_check_if_last_char_is_a_letter_partial_solve_wit_1_aux.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_2 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((txt_pre + ((retval - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i txt_pre (retval - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_3 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((txt_pre + ((retval - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i txt_pre (retval - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p134_check_if_last_char_is_a_letter_partial_solve_wit_4 := 
forall (txt_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full txt_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval <> 1) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth (retval - 1 ) (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_134_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((txt_pre + ((retval - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (retval - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i txt_pre (retval - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_1 : p134_check_if_last_char_is_a_letter_safety_wit_1.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_2 : p134_check_if_last_char_is_a_letter_safety_wit_2.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_3 : p134_check_if_last_char_is_a_letter_safety_wit_3.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_4 : p134_check_if_last_char_is_a_letter_safety_wit_4.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_5 : p134_check_if_last_char_is_a_letter_safety_wit_5.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_6 : p134_check_if_last_char_is_a_letter_safety_wit_6.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_7 : p134_check_if_last_char_is_a_letter_safety_wit_7.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_8 : p134_check_if_last_char_is_a_letter_safety_wit_8.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_9 : p134_check_if_last_char_is_a_letter_safety_wit_9.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_10 : p134_check_if_last_char_is_a_letter_safety_wit_10.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_11 : p134_check_if_last_char_is_a_letter_safety_wit_11.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_12 : p134_check_if_last_char_is_a_letter_safety_wit_12.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_13 : p134_check_if_last_char_is_a_letter_safety_wit_13.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_14 : p134_check_if_last_char_is_a_letter_safety_wit_14.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_15 : p134_check_if_last_char_is_a_letter_safety_wit_15.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_16 : p134_check_if_last_char_is_a_letter_safety_wit_16.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_17 : p134_check_if_last_char_is_a_letter_safety_wit_17.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_18 : p134_check_if_last_char_is_a_letter_safety_wit_18.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_19 : p134_check_if_last_char_is_a_letter_safety_wit_19.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_20 : p134_check_if_last_char_is_a_letter_safety_wit_20.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_21 : p134_check_if_last_char_is_a_letter_safety_wit_21.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_22 : p134_check_if_last_char_is_a_letter_safety_wit_22.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_23 : p134_check_if_last_char_is_a_letter_safety_wit_23.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_24 : p134_check_if_last_char_is_a_letter_safety_wit_24.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_25 : p134_check_if_last_char_is_a_letter_safety_wit_25.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_26 : p134_check_if_last_char_is_a_letter_safety_wit_26.
Axiom proof_of_p134_check_if_last_char_is_a_letter_safety_wit_27 : p134_check_if_last_char_is_a_letter_safety_wit_27.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_1 : p134_check_if_last_char_is_a_letter_return_wit_1.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_2 : p134_check_if_last_char_is_a_letter_return_wit_2.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_3 : p134_check_if_last_char_is_a_letter_return_wit_3.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_4 : p134_check_if_last_char_is_a_letter_return_wit_4.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_5 : p134_check_if_last_char_is_a_letter_return_wit_5.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_6 : p134_check_if_last_char_is_a_letter_return_wit_6.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_7 : p134_check_if_last_char_is_a_letter_return_wit_7.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_8 : p134_check_if_last_char_is_a_letter_return_wit_8.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_9 : p134_check_if_last_char_is_a_letter_return_wit_9.
Axiom proof_of_p134_check_if_last_char_is_a_letter_return_wit_10 : p134_check_if_last_char_is_a_letter_return_wit_10.
Axiom proof_of_p134_check_if_last_char_is_a_letter_partial_solve_wit_1_pure : p134_check_if_last_char_is_a_letter_partial_solve_wit_1_pure.
Axiom proof_of_p134_check_if_last_char_is_a_letter_partial_solve_wit_1 : p134_check_if_last_char_is_a_letter_partial_solve_wit_1.
Axiom proof_of_p134_check_if_last_char_is_a_letter_partial_solve_wit_2 : p134_check_if_last_char_is_a_letter_partial_solve_wit_2.
Axiom proof_of_p134_check_if_last_char_is_a_letter_partial_solve_wit_3 : p134_check_if_last_char_is_a_letter_partial_solve_wit_3.
Axiom proof_of_p134_check_if_last_char_is_a_letter_partial_solve_wit_4 : p134_check_if_last_char_is_a_letter_partial_solve_wit_4.

End VC_Correct.
