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
Require Import p080_is_happy.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p080_is_happy -----*)

Definition p080_is_happy_safety_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p080_is_happy_safety_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p080_is_happy_safety_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p080_is_happy_safety_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p080_is_happy_safety_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = (Znth 1 (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p080_is_happy_safety_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> (Znth 1 (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p080_is_happy_safety_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition p080_is_happy_safety_wit_8 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p080_is_happy_safety_wit_9 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p080_is_happy_safety_wit_10 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 2 )) ”
.

Definition p080_is_happy_safety_wit_11 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p080_is_happy_safety_wit_12 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p080_is_happy_safety_wit_13 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p080_is_happy_safety_wit_14 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p080_is_happy_entail_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) <> (Znth 1 (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= len) ” 
  &&  “ (happy_prefix 2 l ) ” 
  &&  “ (happy_adjacent 2 l ) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_entail_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (happy_prefix (i + 1 ) l ) ” 
  &&  “ (happy_adjacent (i + 1 ) l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_return_wit_1 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_80_spec l 1 ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_return_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_80_spec l 0 ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_return_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_80_spec l 0 ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_return_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ ((Znth 0 (app (l) ((cons (0) (nil)))) 0) = (Znth 1 (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_80_spec l 0 ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_return_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval < 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_80_spec l 0 ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_1_pure := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
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

Definition p080_is_happy_partial_solve_wit_1_aux := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
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
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_1 := p080_is_happy_partial_solve_wit_1_pure -> p080_is_happy_partial_solve_wit_1_aux.

Definition p080_is_happy_partial_solve_wit_2 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((s_pre + (0 * sizeof(CHAR) ) )) # Char  |-> (Znth 0 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre 0 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_3 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (retval >= 3) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((s_pre + (1 * sizeof(CHAR) ) )) # Char  |-> (Znth 1 (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre 1 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_4 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_5 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (((s_pre + ((i - 1 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i - 1 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_6 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p080_is_happy_partial_solve_wit_7 := 
forall (s_pre: Z) (len: Z) (l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (CharArray.full s_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth (i - 1 ) (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < len) ” 
  &&  “ (3 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_80_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (happy_prefix i l ) ” 
  &&  “ (happy_adjacent i l ) ”
  &&  (((s_pre + ((i - 2 ) * sizeof(CHAR) ) )) # Char  |-> (Znth (i - 2 ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre (i - 2 ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p080_is_happy_safety_wit_1 : p080_is_happy_safety_wit_1.
Axiom proof_of_p080_is_happy_safety_wit_2 : p080_is_happy_safety_wit_2.
Axiom proof_of_p080_is_happy_safety_wit_3 : p080_is_happy_safety_wit_3.
Axiom proof_of_p080_is_happy_safety_wit_4 : p080_is_happy_safety_wit_4.
Axiom proof_of_p080_is_happy_safety_wit_5 : p080_is_happy_safety_wit_5.
Axiom proof_of_p080_is_happy_safety_wit_6 : p080_is_happy_safety_wit_6.
Axiom proof_of_p080_is_happy_safety_wit_7 : p080_is_happy_safety_wit_7.
Axiom proof_of_p080_is_happy_safety_wit_8 : p080_is_happy_safety_wit_8.
Axiom proof_of_p080_is_happy_safety_wit_9 : p080_is_happy_safety_wit_9.
Axiom proof_of_p080_is_happy_safety_wit_10 : p080_is_happy_safety_wit_10.
Axiom proof_of_p080_is_happy_safety_wit_11 : p080_is_happy_safety_wit_11.
Axiom proof_of_p080_is_happy_safety_wit_12 : p080_is_happy_safety_wit_12.
Axiom proof_of_p080_is_happy_safety_wit_13 : p080_is_happy_safety_wit_13.
Axiom proof_of_p080_is_happy_safety_wit_14 : p080_is_happy_safety_wit_14.
Axiom proof_of_p080_is_happy_entail_wit_1 : p080_is_happy_entail_wit_1.
Axiom proof_of_p080_is_happy_entail_wit_2 : p080_is_happy_entail_wit_2.
Axiom proof_of_p080_is_happy_return_wit_1 : p080_is_happy_return_wit_1.
Axiom proof_of_p080_is_happy_return_wit_2 : p080_is_happy_return_wit_2.
Axiom proof_of_p080_is_happy_return_wit_3 : p080_is_happy_return_wit_3.
Axiom proof_of_p080_is_happy_return_wit_4 : p080_is_happy_return_wit_4.
Axiom proof_of_p080_is_happy_return_wit_5 : p080_is_happy_return_wit_5.
Axiom proof_of_p080_is_happy_partial_solve_wit_1_pure : p080_is_happy_partial_solve_wit_1_pure.
Axiom proof_of_p080_is_happy_partial_solve_wit_1 : p080_is_happy_partial_solve_wit_1.
Axiom proof_of_p080_is_happy_partial_solve_wit_2 : p080_is_happy_partial_solve_wit_2.
Axiom proof_of_p080_is_happy_partial_solve_wit_3 : p080_is_happy_partial_solve_wit_3.
Axiom proof_of_p080_is_happy_partial_solve_wit_4 : p080_is_happy_partial_solve_wit_4.
Axiom proof_of_p080_is_happy_partial_solve_wit_5 : p080_is_happy_partial_solve_wit_5.
Axiom proof_of_p080_is_happy_partial_solve_wit_6 : p080_is_happy_partial_solve_wit_6.
Axiom proof_of_p080_is_happy_partial_solve_wit_7 : p080_is_happy_partial_solve_wit_7.

End VC_Correct.
