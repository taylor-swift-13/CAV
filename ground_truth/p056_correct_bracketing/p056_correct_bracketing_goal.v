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
Require Import p056_correct_bracketing.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p056_correct_bracketing -----*)

Definition p056_correct_bracketing_safety_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "level" ) )) # Int  |->_)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ (60 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 60) ”
.

Definition p056_correct_bracketing_safety_wit_4 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ ((level + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level + 1 )) ”
.

Definition p056_correct_bracketing_safety_wit_5 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p056_correct_bracketing_safety_wit_6 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ (62 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 62) ”
.

Definition p056_correct_bracketing_safety_wit_7 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ ((level - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (level - 1 )) ”
.

Definition p056_correct_bracketing_safety_wit_8 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p056_correct_bracketing_safety_wit_9 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_10 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_11 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_12 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ False ”
.

Definition p056_correct_bracketing_safety_wit_13 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level + 1 ) < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  “ False ”
.

Definition p056_correct_bracketing_safety_wit_14 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level - 1 ) < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_15 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level + 1 ) >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p056_correct_bracketing_safety_wit_16 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level - 1 ) >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> (level - 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p056_correct_bracketing_safety_wit_17 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p056_correct_bracketing_safety_wit_18 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_19 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level <> 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p056_correct_bracketing_safety_wit_20 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level = 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "level" ) )) # Int  |-> level)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p056_correct_bracketing_entail_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (angle_level_upto (0) (l))) ” 
  &&  “ (angle_nonnegative_prefix 0 l ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_entail_wit_2_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= (i + 1 )) ” 
  &&  “ (level = (angle_level_upto ((i + 1 )) (l))) ” 
  &&  “ (angle_nonnegative_prefix (i + 1 ) l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_entail_wit_2_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level - 1 ) >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (level - 1 )) ” 
  &&  “ ((level - 1 ) <= (i + 1 )) ” 
  &&  “ ((level - 1 ) = (angle_level_upto ((i + 1 )) (l))) ” 
  &&  “ (angle_nonnegative_prefix (i + 1 ) l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_entail_wit_2_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level + 1 ) >= 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= (level + 1 )) ” 
  &&  “ ((level + 1 ) <= (i + 1 )) ” 
  &&  “ ((level + 1 ) = (angle_level_upto ((i + 1 )) (l))) ” 
  &&  “ (angle_nonnegative_prefix (i + 1 ) l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_return_wit_1 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level = 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_56_spec l 1 ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_return_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (level <> 0) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_56_spec l 0 ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_return_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((level - 1 ) < 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 62) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_56_spec l 0 ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_partial_solve_wit_1_pure := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "level" ) )) # Int  |-> 0)
  **  ((( &( "brackets" ) )) # Ptr  |-> brackets_pre)
  **  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p056_correct_bracketing_partial_solve_wit_1_aux := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_partial_solve_wit_1 := p056_correct_bracketing_partial_solve_wit_1_pure -> p056_correct_bracketing_partial_solve_wit_1_aux.

Definition p056_correct_bracketing_partial_solve_wit_2 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (((brackets_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i brackets_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p056_correct_bracketing_partial_solve_wit_3 := 
forall (brackets_pre: Z) (len: Z) (l: (@list Z)) (level: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (CharArray.full brackets_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 60) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_56_pre l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= level) ” 
  &&  “ (level <= i) ” 
  &&  “ (level = (angle_level_upto (i) (l))) ” 
  &&  “ (angle_nonnegative_prefix i l ) ”
  &&  (((brackets_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i brackets_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p056_correct_bracketing_safety_wit_1 : p056_correct_bracketing_safety_wit_1.
Axiom proof_of_p056_correct_bracketing_safety_wit_2 : p056_correct_bracketing_safety_wit_2.
Axiom proof_of_p056_correct_bracketing_safety_wit_3 : p056_correct_bracketing_safety_wit_3.
Axiom proof_of_p056_correct_bracketing_safety_wit_4 : p056_correct_bracketing_safety_wit_4.
Axiom proof_of_p056_correct_bracketing_safety_wit_5 : p056_correct_bracketing_safety_wit_5.
Axiom proof_of_p056_correct_bracketing_safety_wit_6 : p056_correct_bracketing_safety_wit_6.
Axiom proof_of_p056_correct_bracketing_safety_wit_7 : p056_correct_bracketing_safety_wit_7.
Axiom proof_of_p056_correct_bracketing_safety_wit_8 : p056_correct_bracketing_safety_wit_8.
Axiom proof_of_p056_correct_bracketing_safety_wit_9 : p056_correct_bracketing_safety_wit_9.
Axiom proof_of_p056_correct_bracketing_safety_wit_10 : p056_correct_bracketing_safety_wit_10.
Axiom proof_of_p056_correct_bracketing_safety_wit_11 : p056_correct_bracketing_safety_wit_11.
Axiom proof_of_p056_correct_bracketing_safety_wit_12 : p056_correct_bracketing_safety_wit_12.
Axiom proof_of_p056_correct_bracketing_safety_wit_13 : p056_correct_bracketing_safety_wit_13.
Axiom proof_of_p056_correct_bracketing_safety_wit_14 : p056_correct_bracketing_safety_wit_14.
Axiom proof_of_p056_correct_bracketing_safety_wit_15 : p056_correct_bracketing_safety_wit_15.
Axiom proof_of_p056_correct_bracketing_safety_wit_16 : p056_correct_bracketing_safety_wit_16.
Axiom proof_of_p056_correct_bracketing_safety_wit_17 : p056_correct_bracketing_safety_wit_17.
Axiom proof_of_p056_correct_bracketing_safety_wit_18 : p056_correct_bracketing_safety_wit_18.
Axiom proof_of_p056_correct_bracketing_safety_wit_19 : p056_correct_bracketing_safety_wit_19.
Axiom proof_of_p056_correct_bracketing_safety_wit_20 : p056_correct_bracketing_safety_wit_20.
Axiom proof_of_p056_correct_bracketing_entail_wit_1 : p056_correct_bracketing_entail_wit_1.
Axiom proof_of_p056_correct_bracketing_entail_wit_2_1 : p056_correct_bracketing_entail_wit_2_1.
Axiom proof_of_p056_correct_bracketing_entail_wit_2_2 : p056_correct_bracketing_entail_wit_2_2.
Axiom proof_of_p056_correct_bracketing_entail_wit_2_3 : p056_correct_bracketing_entail_wit_2_3.
Axiom proof_of_p056_correct_bracketing_return_wit_1 : p056_correct_bracketing_return_wit_1.
Axiom proof_of_p056_correct_bracketing_return_wit_2 : p056_correct_bracketing_return_wit_2.
Axiom proof_of_p056_correct_bracketing_return_wit_3 : p056_correct_bracketing_return_wit_3.
Axiom proof_of_p056_correct_bracketing_partial_solve_wit_1_pure : p056_correct_bracketing_partial_solve_wit_1_pure.
Axiom proof_of_p056_correct_bracketing_partial_solve_wit_1 : p056_correct_bracketing_partial_solve_wit_1.
Axiom proof_of_p056_correct_bracketing_partial_solve_wit_2 : p056_correct_bracketing_partial_solve_wit_2.
Axiom proof_of_p056_correct_bracketing_partial_solve_wit_3 : p056_correct_bracketing_partial_solve_wit_3.

End VC_Correct.
