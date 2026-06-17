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
Require Import p141_file_name_check.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p141_file_name_check -----*)

Definition p141_file_name_check_safety_wit_1 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "numdigit" ) )) # Int  |->_)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "numdot" ) )) # Int  |->_)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "alpha" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_5 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "suffix" ) )) # Int  |->_)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_6 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (5 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 5) ”
.

Definition p141_file_name_check_safety_wit_7 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_8 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "w" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_9 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p141_file_name_check_safety_wit_10 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p141_file_name_check_safety_wit_11 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_12 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (97 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 97) ”
.

Definition p141_file_name_check_safety_wit_13 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (122 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 122) ”
.

Definition p141_file_name_check_safety_wit_14 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "w" ) )) # Int  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_15 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_16 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_17 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_18 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_19 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_20 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c0" ) )) # Int  |->_)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((len - 4 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 4 )) ”
.

Definition p141_file_name_check_safety_wit_21 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c0" ) )) # Int  |->_)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (4 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 4) ”
.

Definition p141_file_name_check_safety_wit_22 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c1" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ ((len - 3 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 3 )) ”
.

Definition p141_file_name_check_safety_wit_23 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c1" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p141_file_name_check_safety_wit_24 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c2" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ ((len - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 2 )) ”
.

Definition p141_file_name_check_safety_wit_25 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c2" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p141_file_name_check_safety_wit_26 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c3" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ ((len - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len - 1 )) ”
.

Definition p141_file_name_check_safety_wit_27 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "c3" ) )) # Int  |->_)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_28 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p141_file_name_check_safety_wit_29 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (116 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 116) ”
.

Definition p141_file_name_check_safety_wit_30 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (120 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 120) ”
.

Definition p141_file_name_check_safety_wit_31 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (116 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 116) ”
.

Definition p141_file_name_check_safety_wit_32 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_33 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p141_file_name_check_safety_wit_34 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p141_file_name_check_safety_wit_35 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p141_file_name_check_safety_wit_36 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p141_file_name_check_safety_wit_37 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_38 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_39 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_40 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (120 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 120) ”
.

Definition p141_file_name_check_safety_wit_41 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (101 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 101) ”
.

Definition p141_file_name_check_safety_wit_42 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_43 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_44 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_45 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_46 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_47 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_48 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_49 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p141_file_name_check_safety_wit_50 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_51 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_52 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_53 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_54 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_55 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_56 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (108 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 108) ”
.

Definition p141_file_name_check_safety_wit_57 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (108 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 108) ”
.

Definition p141_file_name_check_safety_wit_58 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c3" ) )) # Int  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c2" ) )) # Int  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c1" ) )) # Int  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "c0" ) )) # Int  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_59 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) (suffix: Z) (alpha: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_60 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) (suffix: Z) (alpha: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_61 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) (suffix: Z) (alpha: Z) ,
  “ (suffix <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_62 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) (suffix: Z) (alpha: Z) ,
  “ (suffix = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_63 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) (suffix: Z) (alpha: Z) ,
  “ (suffix = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_64 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p141_file_name_check_safety_wit_65 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (57 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 57) ”
.

Definition p141_file_name_check_safety_wit_66 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ ((numdigit + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numdigit + 1 )) ”
.

Definition p141_file_name_check_safety_wit_67 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_68 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p141_file_name_check_safety_wit_69 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p141_file_name_check_safety_wit_70 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> (numdigit + 1 ))
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p141_file_name_check_safety_wit_71 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_72 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> (numdigit + 1 ))
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ False ”
.

Definition p141_file_name_check_safety_wit_73 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ ((numdot + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numdot + 1 )) ”
.

Definition p141_file_name_check_safety_wit_74 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_75 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> (numdigit + 1 ))
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p141_file_name_check_safety_wit_76 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> (numdigit + 1 ))
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_77 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p141_file_name_check_safety_wit_78 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_79 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p141_file_name_check_safety_wit_80 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_81 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> (numdot + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p141_file_name_check_safety_wit_82 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> (numdot + 1 ))
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_83 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p141_file_name_check_safety_wit_84 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ (numdigit > 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_85 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ (numdigit <= 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_safety_wit_86 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (c3: Z) (c2: Z) (c1: Z) (c0: Z) (w: Z) (suffix: Z) (alpha: Z) ,
  “ (numdot <> 1) ” 
  &&  “ (numdigit <= 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p141_file_name_check_safety_wit_87 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) (w: Z) (c0: Z) (c1: Z) (c2: Z) (c3: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (file_name_checks l ) ”
  &&  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "numdigit" ) )) # Int  |-> numdigit)
  **  ((( &( "numdot" ) )) # Int  |-> numdot)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "alpha" ) )) # Int  |-> alpha)
  **  ((( &( "suffix" ) )) # Int  |-> suffix)
  **  ((( &( "w" ) )) # Int  |-> w)
  **  ((( &( "c0" ) )) # Int  |-> c0)
  **  ((( &( "c1" ) )) # Int  |-> c1)
  **  ((( &( "c2" ) )) # Int  |-> c2)
  **  ((( &( "c3" ) )) # Int  |-> c3)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p141_file_name_check_entail_wit_1_1 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_1_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <= 122) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (1 = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_1_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 122) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 97) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_1_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) < 97) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_1_5 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_1 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 108) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 108) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 108) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_5 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_6 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_7 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_8 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) <> 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_9 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) <> 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_10 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 100) ” 
  &&  “ ((Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0) = 120) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) = 101) ” 
  &&  “ ((Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0) <> 116) ” 
  &&  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (1 = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_2_11 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ ((Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p141_file_name_check_entail_wit_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (suffix <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_5_1 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= (i + 1 )) ” 
  &&  “ (0 <= (numdot + 1 )) ” 
  &&  “ ((numdot + 1 ) <= (i + 1 )) ” 
  &&  “ (numdigit = (digit_count_upto ((i + 1 )) (l))) ” 
  &&  “ ((numdot + 1 ) = (dot_count_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_5_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= (i + 1 )) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= (i + 1 )) ” 
  &&  “ (numdigit = (digit_count_upto ((i + 1 )) (l))) ” 
  &&  “ (numdot = (dot_count_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_5_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= (i + 1 )) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= (i + 1 )) ” 
  &&  “ (numdigit = (digit_count_upto ((i + 1 )) (l))) ” 
  &&  “ (numdot = (dot_count_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_5_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (numdigit + 1 )) ” 
  &&  “ ((numdigit + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= (i + 1 )) ” 
  &&  “ ((numdigit + 1 ) = (digit_count_upto ((i + 1 )) (l))) ” 
  &&  “ (numdot = (dot_count_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_entail_wit_6 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (numdot = 1) ” 
  &&  “ (numdigit <= 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (file_name_checks l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_1 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (alpha: Z) (suffix: Z) ,
  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (file_name_checks l ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 1 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (numdot <> 1) ” 
  &&  “ (numdigit <= 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 0 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (numdigit > 3) ” 
  &&  “ (i >= len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 0 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (suffix = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix = 0) ” 
  &&  “ ~((suffix_ok l )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 0 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_5 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha = 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 0) ” 
  &&  “ ~((is_alpha (Znth (0) (l) (0)) )) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 0 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_return_wit_6 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_141_spec l 0 ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_1_pure := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "suffix" ) )) # Int  |-> 0)
  **  ((( &( "alpha" ) )) # Int  |-> 0)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "numdot" ) )) # Int  |-> 0)
  **  ((( &( "numdigit" ) )) # Int  |-> 0)
  **  ((( &( "file_name" ) )) # Ptr  |-> file_name_pre)
  **  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p141_file_name_check_partial_solve_wit_1_aux := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_1 := p141_file_name_check_partial_solve_wit_1_pure -> p141_file_name_check_partial_solve_wit_1_aux.

Definition p141_file_name_check_partial_solve_wit_2 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval >= 5) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((file_name_pre + (0 * sizeof(CHAR) ) )) # Char  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre 0 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_3 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (((file_name_pre + ((len - 4 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 4 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre (len - 4 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_4 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (((file_name_pre + ((len - 3 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 3 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre (len - 3 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_5 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (((file_name_pre + ((len - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre (len - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_6 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdigit: Z) (numdot: Z) (i: Z) (alpha: Z) (suffix: Z) ,
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (alpha <> 0) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (numdigit = 0) ” 
  &&  “ (numdot = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (suffix = 0) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ”
  &&  (((file_name_pre + ((len - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (len - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre (len - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_7 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (((file_name_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_8 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (((file_name_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_9 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (((file_name_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_10 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (((file_name_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p141_file_name_check_partial_solve_wit_11 := 
forall (file_name_pre: Z) (len: Z) (l: (@list Z)) (numdot: Z) (numdigit: Z) (i: Z) (suffix: Z) (alpha: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (CharArray.full file_name_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 57) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 48) ” 
  &&  “ (i < len) ” 
  &&  “ (5 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_141_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (alpha = 1) ” 
  &&  “ (suffix = 1) ” 
  &&  “ (is_alpha (Znth (0) (l) (0)) ) ” 
  &&  “ (suffix_ok l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= numdigit) ” 
  &&  “ (numdigit <= i) ” 
  &&  “ (0 <= numdot) ” 
  &&  “ (numdot <= i) ” 
  &&  “ (numdigit = (digit_count_upto (i) (l))) ” 
  &&  “ (numdot = (dot_count_upto (i) (l))) ”
  &&  (((file_name_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i file_name_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p141_file_name_check_safety_wit_1 : p141_file_name_check_safety_wit_1.
Axiom proof_of_p141_file_name_check_safety_wit_2 : p141_file_name_check_safety_wit_2.
Axiom proof_of_p141_file_name_check_safety_wit_3 : p141_file_name_check_safety_wit_3.
Axiom proof_of_p141_file_name_check_safety_wit_4 : p141_file_name_check_safety_wit_4.
Axiom proof_of_p141_file_name_check_safety_wit_5 : p141_file_name_check_safety_wit_5.
Axiom proof_of_p141_file_name_check_safety_wit_6 : p141_file_name_check_safety_wit_6.
Axiom proof_of_p141_file_name_check_safety_wit_7 : p141_file_name_check_safety_wit_7.
Axiom proof_of_p141_file_name_check_safety_wit_8 : p141_file_name_check_safety_wit_8.
Axiom proof_of_p141_file_name_check_safety_wit_9 : p141_file_name_check_safety_wit_9.
Axiom proof_of_p141_file_name_check_safety_wit_10 : p141_file_name_check_safety_wit_10.
Axiom proof_of_p141_file_name_check_safety_wit_11 : p141_file_name_check_safety_wit_11.
Axiom proof_of_p141_file_name_check_safety_wit_12 : p141_file_name_check_safety_wit_12.
Axiom proof_of_p141_file_name_check_safety_wit_13 : p141_file_name_check_safety_wit_13.
Axiom proof_of_p141_file_name_check_safety_wit_14 : p141_file_name_check_safety_wit_14.
Axiom proof_of_p141_file_name_check_safety_wit_15 : p141_file_name_check_safety_wit_15.
Axiom proof_of_p141_file_name_check_safety_wit_16 : p141_file_name_check_safety_wit_16.
Axiom proof_of_p141_file_name_check_safety_wit_17 : p141_file_name_check_safety_wit_17.
Axiom proof_of_p141_file_name_check_safety_wit_18 : p141_file_name_check_safety_wit_18.
Axiom proof_of_p141_file_name_check_safety_wit_19 : p141_file_name_check_safety_wit_19.
Axiom proof_of_p141_file_name_check_safety_wit_20 : p141_file_name_check_safety_wit_20.
Axiom proof_of_p141_file_name_check_safety_wit_21 : p141_file_name_check_safety_wit_21.
Axiom proof_of_p141_file_name_check_safety_wit_22 : p141_file_name_check_safety_wit_22.
Axiom proof_of_p141_file_name_check_safety_wit_23 : p141_file_name_check_safety_wit_23.
Axiom proof_of_p141_file_name_check_safety_wit_24 : p141_file_name_check_safety_wit_24.
Axiom proof_of_p141_file_name_check_safety_wit_25 : p141_file_name_check_safety_wit_25.
Axiom proof_of_p141_file_name_check_safety_wit_26 : p141_file_name_check_safety_wit_26.
Axiom proof_of_p141_file_name_check_safety_wit_27 : p141_file_name_check_safety_wit_27.
Axiom proof_of_p141_file_name_check_safety_wit_28 : p141_file_name_check_safety_wit_28.
Axiom proof_of_p141_file_name_check_safety_wit_29 : p141_file_name_check_safety_wit_29.
Axiom proof_of_p141_file_name_check_safety_wit_30 : p141_file_name_check_safety_wit_30.
Axiom proof_of_p141_file_name_check_safety_wit_31 : p141_file_name_check_safety_wit_31.
Axiom proof_of_p141_file_name_check_safety_wit_32 : p141_file_name_check_safety_wit_32.
Axiom proof_of_p141_file_name_check_safety_wit_33 : p141_file_name_check_safety_wit_33.
Axiom proof_of_p141_file_name_check_safety_wit_34 : p141_file_name_check_safety_wit_34.
Axiom proof_of_p141_file_name_check_safety_wit_35 : p141_file_name_check_safety_wit_35.
Axiom proof_of_p141_file_name_check_safety_wit_36 : p141_file_name_check_safety_wit_36.
Axiom proof_of_p141_file_name_check_safety_wit_37 : p141_file_name_check_safety_wit_37.
Axiom proof_of_p141_file_name_check_safety_wit_38 : p141_file_name_check_safety_wit_38.
Axiom proof_of_p141_file_name_check_safety_wit_39 : p141_file_name_check_safety_wit_39.
Axiom proof_of_p141_file_name_check_safety_wit_40 : p141_file_name_check_safety_wit_40.
Axiom proof_of_p141_file_name_check_safety_wit_41 : p141_file_name_check_safety_wit_41.
Axiom proof_of_p141_file_name_check_safety_wit_42 : p141_file_name_check_safety_wit_42.
Axiom proof_of_p141_file_name_check_safety_wit_43 : p141_file_name_check_safety_wit_43.
Axiom proof_of_p141_file_name_check_safety_wit_44 : p141_file_name_check_safety_wit_44.
Axiom proof_of_p141_file_name_check_safety_wit_45 : p141_file_name_check_safety_wit_45.
Axiom proof_of_p141_file_name_check_safety_wit_46 : p141_file_name_check_safety_wit_46.
Axiom proof_of_p141_file_name_check_safety_wit_47 : p141_file_name_check_safety_wit_47.
Axiom proof_of_p141_file_name_check_safety_wit_48 : p141_file_name_check_safety_wit_48.
Axiom proof_of_p141_file_name_check_safety_wit_49 : p141_file_name_check_safety_wit_49.
Axiom proof_of_p141_file_name_check_safety_wit_50 : p141_file_name_check_safety_wit_50.
Axiom proof_of_p141_file_name_check_safety_wit_51 : p141_file_name_check_safety_wit_51.
Axiom proof_of_p141_file_name_check_safety_wit_52 : p141_file_name_check_safety_wit_52.
Axiom proof_of_p141_file_name_check_safety_wit_53 : p141_file_name_check_safety_wit_53.
Axiom proof_of_p141_file_name_check_safety_wit_54 : p141_file_name_check_safety_wit_54.
Axiom proof_of_p141_file_name_check_safety_wit_55 : p141_file_name_check_safety_wit_55.
Axiom proof_of_p141_file_name_check_safety_wit_56 : p141_file_name_check_safety_wit_56.
Axiom proof_of_p141_file_name_check_safety_wit_57 : p141_file_name_check_safety_wit_57.
Axiom proof_of_p141_file_name_check_safety_wit_58 : p141_file_name_check_safety_wit_58.
Axiom proof_of_p141_file_name_check_safety_wit_59 : p141_file_name_check_safety_wit_59.
Axiom proof_of_p141_file_name_check_safety_wit_60 : p141_file_name_check_safety_wit_60.
Axiom proof_of_p141_file_name_check_safety_wit_61 : p141_file_name_check_safety_wit_61.
Axiom proof_of_p141_file_name_check_safety_wit_62 : p141_file_name_check_safety_wit_62.
Axiom proof_of_p141_file_name_check_safety_wit_63 : p141_file_name_check_safety_wit_63.
Axiom proof_of_p141_file_name_check_safety_wit_64 : p141_file_name_check_safety_wit_64.
Axiom proof_of_p141_file_name_check_safety_wit_65 : p141_file_name_check_safety_wit_65.
Axiom proof_of_p141_file_name_check_safety_wit_66 : p141_file_name_check_safety_wit_66.
Axiom proof_of_p141_file_name_check_safety_wit_67 : p141_file_name_check_safety_wit_67.
Axiom proof_of_p141_file_name_check_safety_wit_68 : p141_file_name_check_safety_wit_68.
Axiom proof_of_p141_file_name_check_safety_wit_69 : p141_file_name_check_safety_wit_69.
Axiom proof_of_p141_file_name_check_safety_wit_70 : p141_file_name_check_safety_wit_70.
Axiom proof_of_p141_file_name_check_safety_wit_71 : p141_file_name_check_safety_wit_71.
Axiom proof_of_p141_file_name_check_safety_wit_72 : p141_file_name_check_safety_wit_72.
Axiom proof_of_p141_file_name_check_safety_wit_73 : p141_file_name_check_safety_wit_73.
Axiom proof_of_p141_file_name_check_safety_wit_74 : p141_file_name_check_safety_wit_74.
Axiom proof_of_p141_file_name_check_safety_wit_75 : p141_file_name_check_safety_wit_75.
Axiom proof_of_p141_file_name_check_safety_wit_76 : p141_file_name_check_safety_wit_76.
Axiom proof_of_p141_file_name_check_safety_wit_77 : p141_file_name_check_safety_wit_77.
Axiom proof_of_p141_file_name_check_safety_wit_78 : p141_file_name_check_safety_wit_78.
Axiom proof_of_p141_file_name_check_safety_wit_79 : p141_file_name_check_safety_wit_79.
Axiom proof_of_p141_file_name_check_safety_wit_80 : p141_file_name_check_safety_wit_80.
Axiom proof_of_p141_file_name_check_safety_wit_81 : p141_file_name_check_safety_wit_81.
Axiom proof_of_p141_file_name_check_safety_wit_82 : p141_file_name_check_safety_wit_82.
Axiom proof_of_p141_file_name_check_safety_wit_83 : p141_file_name_check_safety_wit_83.
Axiom proof_of_p141_file_name_check_safety_wit_84 : p141_file_name_check_safety_wit_84.
Axiom proof_of_p141_file_name_check_safety_wit_85 : p141_file_name_check_safety_wit_85.
Axiom proof_of_p141_file_name_check_safety_wit_86 : p141_file_name_check_safety_wit_86.
Axiom proof_of_p141_file_name_check_safety_wit_87 : p141_file_name_check_safety_wit_87.
Axiom proof_of_p141_file_name_check_entail_wit_1_1 : p141_file_name_check_entail_wit_1_1.
Axiom proof_of_p141_file_name_check_entail_wit_1_2 : p141_file_name_check_entail_wit_1_2.
Axiom proof_of_p141_file_name_check_entail_wit_1_3 : p141_file_name_check_entail_wit_1_3.
Axiom proof_of_p141_file_name_check_entail_wit_1_4 : p141_file_name_check_entail_wit_1_4.
Axiom proof_of_p141_file_name_check_entail_wit_1_5 : p141_file_name_check_entail_wit_1_5.
Axiom proof_of_p141_file_name_check_entail_wit_2_1 : p141_file_name_check_entail_wit_2_1.
Axiom proof_of_p141_file_name_check_entail_wit_2_2 : p141_file_name_check_entail_wit_2_2.
Axiom proof_of_p141_file_name_check_entail_wit_2_3 : p141_file_name_check_entail_wit_2_3.
Axiom proof_of_p141_file_name_check_entail_wit_2_4 : p141_file_name_check_entail_wit_2_4.
Axiom proof_of_p141_file_name_check_entail_wit_2_5 : p141_file_name_check_entail_wit_2_5.
Axiom proof_of_p141_file_name_check_entail_wit_2_6 : p141_file_name_check_entail_wit_2_6.
Axiom proof_of_p141_file_name_check_entail_wit_2_7 : p141_file_name_check_entail_wit_2_7.
Axiom proof_of_p141_file_name_check_entail_wit_2_8 : p141_file_name_check_entail_wit_2_8.
Axiom proof_of_p141_file_name_check_entail_wit_2_9 : p141_file_name_check_entail_wit_2_9.
Axiom proof_of_p141_file_name_check_entail_wit_2_10 : p141_file_name_check_entail_wit_2_10.
Axiom proof_of_p141_file_name_check_entail_wit_2_11 : p141_file_name_check_entail_wit_2_11.
Axiom proof_of_p141_file_name_check_entail_wit_3 : p141_file_name_check_entail_wit_3.
Axiom proof_of_p141_file_name_check_entail_wit_4 : p141_file_name_check_entail_wit_4.
Axiom proof_of_p141_file_name_check_entail_wit_5_1 : p141_file_name_check_entail_wit_5_1.
Axiom proof_of_p141_file_name_check_entail_wit_5_2 : p141_file_name_check_entail_wit_5_2.
Axiom proof_of_p141_file_name_check_entail_wit_5_3 : p141_file_name_check_entail_wit_5_3.
Axiom proof_of_p141_file_name_check_entail_wit_5_4 : p141_file_name_check_entail_wit_5_4.
Axiom proof_of_p141_file_name_check_entail_wit_6 : p141_file_name_check_entail_wit_6.
Axiom proof_of_p141_file_name_check_return_wit_1 : p141_file_name_check_return_wit_1.
Axiom proof_of_p141_file_name_check_return_wit_2 : p141_file_name_check_return_wit_2.
Axiom proof_of_p141_file_name_check_return_wit_3 : p141_file_name_check_return_wit_3.
Axiom proof_of_p141_file_name_check_return_wit_4 : p141_file_name_check_return_wit_4.
Axiom proof_of_p141_file_name_check_return_wit_5 : p141_file_name_check_return_wit_5.
Axiom proof_of_p141_file_name_check_return_wit_6 : p141_file_name_check_return_wit_6.
Axiom proof_of_p141_file_name_check_partial_solve_wit_1_pure : p141_file_name_check_partial_solve_wit_1_pure.
Axiom proof_of_p141_file_name_check_partial_solve_wit_1 : p141_file_name_check_partial_solve_wit_1.
Axiom proof_of_p141_file_name_check_partial_solve_wit_2 : p141_file_name_check_partial_solve_wit_2.
Axiom proof_of_p141_file_name_check_partial_solve_wit_3 : p141_file_name_check_partial_solve_wit_3.
Axiom proof_of_p141_file_name_check_partial_solve_wit_4 : p141_file_name_check_partial_solve_wit_4.
Axiom proof_of_p141_file_name_check_partial_solve_wit_5 : p141_file_name_check_partial_solve_wit_5.
Axiom proof_of_p141_file_name_check_partial_solve_wit_6 : p141_file_name_check_partial_solve_wit_6.
Axiom proof_of_p141_file_name_check_partial_solve_wit_7 : p141_file_name_check_partial_solve_wit_7.
Axiom proof_of_p141_file_name_check_partial_solve_wit_8 : p141_file_name_check_partial_solve_wit_8.
Axiom proof_of_p141_file_name_check_partial_solve_wit_9 : p141_file_name_check_partial_solve_wit_9.
Axiom proof_of_p141_file_name_check_partial_solve_wit_10 : p141_file_name_check_partial_solve_wit_10.
Axiom proof_of_p141_file_name_check_partial_solve_wit_11 : p141_file_name_check_partial_solve_wit_11.

End VC_Correct.
