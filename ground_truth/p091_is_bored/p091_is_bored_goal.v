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
Require Import p091_is_bored.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p091_is_bored -----*)

Definition p091_is_bored_safety_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "isstart" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "isi" ) )) # Int  |->_)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_3 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_4 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_5 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_6 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_7 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_8 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((sum + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + 1 )) ”
.

Definition p091_is_bored_safety_wit_9 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_10 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition p091_is_bored_safety_wit_11 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition p091_is_bored_safety_wit_12 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (73 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 73) ”
.

Definition p091_is_bored_safety_wit_13 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_14 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_15 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_16 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_17 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_18 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_19 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> isi)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_20 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_21 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_22 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_23 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_24 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_25 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p091_is_bored_safety_wit_26 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_27 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_28 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_29 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_30 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_31 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_32 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_33 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p091_is_bored_safety_wit_34 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p091_is_bored_safety_wit_35 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p091_is_bored_safety_wit_36 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p091_is_bored_safety_wit_37 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p091_is_bored_safety_wit_38 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ (46 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 46) ”
.

Definition p091_is_bored_safety_wit_39 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_40 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_41 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_42 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_43 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition p091_is_bored_safety_wit_44 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition p091_is_bored_safety_wit_45 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition p091_is_bored_safety_wit_46 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition p091_is_bored_safety_wit_47 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (63 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 63) ”
.

Definition p091_is_bored_safety_wit_48 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_49 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_50 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_51 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_52 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition p091_is_bored_safety_wit_53 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition p091_is_bored_safety_wit_54 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition p091_is_bored_safety_wit_55 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition p091_is_bored_safety_wit_56 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (33 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 33) ”
.

Definition p091_is_bored_safety_wit_57 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_58 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_59 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_60 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ False ”
.

Definition p091_is_bored_safety_wit_61 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_62 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_63 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p091_is_bored_safety_wit_64 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_65 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_66 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_67 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> (sum + 1 ))
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_68 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> isstart)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_69 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_70 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_safety_wit_71 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "isi" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p091_is_bored_entail_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (0 = (bored_sum_prefix (0) (l))) ” 
  &&  “ (1 = (bored_isstart_prefix (0) (l))) ” 
  &&  “ (0 = (bored_isi_prefix (0) (l))) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (1 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (1 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_3 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (1 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_4 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_5 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ (isi = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ ((sum + 1 ) = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= (sum + 1 )) ” 
  &&  “ ((sum + 1 ) <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_6 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_7 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart <> 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_entail_wit_2_8 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 33) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 63) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 46) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (isstart = 1) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 73) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 32) ” 
  &&  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (sum = (bored_sum_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 = (bored_isstart_prefix ((i + 1 )) (l))) ” 
  &&  “ (1 = (bored_isi_prefix ((i + 1 )) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= (i + 1 )) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_return_wit_1 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (i >= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_91_spec l sum ) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_partial_solve_wit_1_pure := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "sum" ) )) # Int  |-> 0)
  **  ((( &( "isi" ) )) # Int  |-> 0)
  **  ((( &( "isstart" ) )) # Int  |-> 1)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "S" ) )) # Ptr  |-> S_pre)
  **  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p091_is_bored_partial_solve_wit_1_aux := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p091_is_bored_partial_solve_wit_1 := p091_is_bored_partial_solve_wit_1_pure -> p091_is_bored_partial_solve_wit_1_aux.

Definition p091_is_bored_partial_solve_wit_2 := 
forall (S_pre: Z) (len: Z) (l: (@list Z)) (isi: Z) (isstart: Z) (sum: Z) (i: Z) ,
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (CharArray.full S_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (problem_91_pre l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (sum = (bored_sum_prefix (i) (l))) ” 
  &&  “ (isstart = (bored_isstart_prefix (i) (l))) ” 
  &&  “ (isi = (bored_isi_prefix (i) (l))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ (sum <= i) ”
  &&  (((S_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i S_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p091_is_bored_safety_wit_1 : p091_is_bored_safety_wit_1.
Axiom proof_of_p091_is_bored_safety_wit_2 : p091_is_bored_safety_wit_2.
Axiom proof_of_p091_is_bored_safety_wit_3 : p091_is_bored_safety_wit_3.
Axiom proof_of_p091_is_bored_safety_wit_4 : p091_is_bored_safety_wit_4.
Axiom proof_of_p091_is_bored_safety_wit_5 : p091_is_bored_safety_wit_5.
Axiom proof_of_p091_is_bored_safety_wit_6 : p091_is_bored_safety_wit_6.
Axiom proof_of_p091_is_bored_safety_wit_7 : p091_is_bored_safety_wit_7.
Axiom proof_of_p091_is_bored_safety_wit_8 : p091_is_bored_safety_wit_8.
Axiom proof_of_p091_is_bored_safety_wit_9 : p091_is_bored_safety_wit_9.
Axiom proof_of_p091_is_bored_safety_wit_10 : p091_is_bored_safety_wit_10.
Axiom proof_of_p091_is_bored_safety_wit_11 : p091_is_bored_safety_wit_11.
Axiom proof_of_p091_is_bored_safety_wit_12 : p091_is_bored_safety_wit_12.
Axiom proof_of_p091_is_bored_safety_wit_13 : p091_is_bored_safety_wit_13.
Axiom proof_of_p091_is_bored_safety_wit_14 : p091_is_bored_safety_wit_14.
Axiom proof_of_p091_is_bored_safety_wit_15 : p091_is_bored_safety_wit_15.
Axiom proof_of_p091_is_bored_safety_wit_16 : p091_is_bored_safety_wit_16.
Axiom proof_of_p091_is_bored_safety_wit_17 : p091_is_bored_safety_wit_17.
Axiom proof_of_p091_is_bored_safety_wit_18 : p091_is_bored_safety_wit_18.
Axiom proof_of_p091_is_bored_safety_wit_19 : p091_is_bored_safety_wit_19.
Axiom proof_of_p091_is_bored_safety_wit_20 : p091_is_bored_safety_wit_20.
Axiom proof_of_p091_is_bored_safety_wit_21 : p091_is_bored_safety_wit_21.
Axiom proof_of_p091_is_bored_safety_wit_22 : p091_is_bored_safety_wit_22.
Axiom proof_of_p091_is_bored_safety_wit_23 : p091_is_bored_safety_wit_23.
Axiom proof_of_p091_is_bored_safety_wit_24 : p091_is_bored_safety_wit_24.
Axiom proof_of_p091_is_bored_safety_wit_25 : p091_is_bored_safety_wit_25.
Axiom proof_of_p091_is_bored_safety_wit_26 : p091_is_bored_safety_wit_26.
Axiom proof_of_p091_is_bored_safety_wit_27 : p091_is_bored_safety_wit_27.
Axiom proof_of_p091_is_bored_safety_wit_28 : p091_is_bored_safety_wit_28.
Axiom proof_of_p091_is_bored_safety_wit_29 : p091_is_bored_safety_wit_29.
Axiom proof_of_p091_is_bored_safety_wit_30 : p091_is_bored_safety_wit_30.
Axiom proof_of_p091_is_bored_safety_wit_31 : p091_is_bored_safety_wit_31.
Axiom proof_of_p091_is_bored_safety_wit_32 : p091_is_bored_safety_wit_32.
Axiom proof_of_p091_is_bored_safety_wit_33 : p091_is_bored_safety_wit_33.
Axiom proof_of_p091_is_bored_safety_wit_34 : p091_is_bored_safety_wit_34.
Axiom proof_of_p091_is_bored_safety_wit_35 : p091_is_bored_safety_wit_35.
Axiom proof_of_p091_is_bored_safety_wit_36 : p091_is_bored_safety_wit_36.
Axiom proof_of_p091_is_bored_safety_wit_37 : p091_is_bored_safety_wit_37.
Axiom proof_of_p091_is_bored_safety_wit_38 : p091_is_bored_safety_wit_38.
Axiom proof_of_p091_is_bored_safety_wit_39 : p091_is_bored_safety_wit_39.
Axiom proof_of_p091_is_bored_safety_wit_40 : p091_is_bored_safety_wit_40.
Axiom proof_of_p091_is_bored_safety_wit_41 : p091_is_bored_safety_wit_41.
Axiom proof_of_p091_is_bored_safety_wit_42 : p091_is_bored_safety_wit_42.
Axiom proof_of_p091_is_bored_safety_wit_43 : p091_is_bored_safety_wit_43.
Axiom proof_of_p091_is_bored_safety_wit_44 : p091_is_bored_safety_wit_44.
Axiom proof_of_p091_is_bored_safety_wit_45 : p091_is_bored_safety_wit_45.
Axiom proof_of_p091_is_bored_safety_wit_46 : p091_is_bored_safety_wit_46.
Axiom proof_of_p091_is_bored_safety_wit_47 : p091_is_bored_safety_wit_47.
Axiom proof_of_p091_is_bored_safety_wit_48 : p091_is_bored_safety_wit_48.
Axiom proof_of_p091_is_bored_safety_wit_49 : p091_is_bored_safety_wit_49.
Axiom proof_of_p091_is_bored_safety_wit_50 : p091_is_bored_safety_wit_50.
Axiom proof_of_p091_is_bored_safety_wit_51 : p091_is_bored_safety_wit_51.
Axiom proof_of_p091_is_bored_safety_wit_52 : p091_is_bored_safety_wit_52.
Axiom proof_of_p091_is_bored_safety_wit_53 : p091_is_bored_safety_wit_53.
Axiom proof_of_p091_is_bored_safety_wit_54 : p091_is_bored_safety_wit_54.
Axiom proof_of_p091_is_bored_safety_wit_55 : p091_is_bored_safety_wit_55.
Axiom proof_of_p091_is_bored_safety_wit_56 : p091_is_bored_safety_wit_56.
Axiom proof_of_p091_is_bored_safety_wit_57 : p091_is_bored_safety_wit_57.
Axiom proof_of_p091_is_bored_safety_wit_58 : p091_is_bored_safety_wit_58.
Axiom proof_of_p091_is_bored_safety_wit_59 : p091_is_bored_safety_wit_59.
Axiom proof_of_p091_is_bored_safety_wit_60 : p091_is_bored_safety_wit_60.
Axiom proof_of_p091_is_bored_safety_wit_61 : p091_is_bored_safety_wit_61.
Axiom proof_of_p091_is_bored_safety_wit_62 : p091_is_bored_safety_wit_62.
Axiom proof_of_p091_is_bored_safety_wit_63 : p091_is_bored_safety_wit_63.
Axiom proof_of_p091_is_bored_safety_wit_64 : p091_is_bored_safety_wit_64.
Axiom proof_of_p091_is_bored_safety_wit_65 : p091_is_bored_safety_wit_65.
Axiom proof_of_p091_is_bored_safety_wit_66 : p091_is_bored_safety_wit_66.
Axiom proof_of_p091_is_bored_safety_wit_67 : p091_is_bored_safety_wit_67.
Axiom proof_of_p091_is_bored_safety_wit_68 : p091_is_bored_safety_wit_68.
Axiom proof_of_p091_is_bored_safety_wit_69 : p091_is_bored_safety_wit_69.
Axiom proof_of_p091_is_bored_safety_wit_70 : p091_is_bored_safety_wit_70.
Axiom proof_of_p091_is_bored_safety_wit_71 : p091_is_bored_safety_wit_71.
Axiom proof_of_p091_is_bored_entail_wit_1 : p091_is_bored_entail_wit_1.
Axiom proof_of_p091_is_bored_entail_wit_2_1 : p091_is_bored_entail_wit_2_1.
Axiom proof_of_p091_is_bored_entail_wit_2_2 : p091_is_bored_entail_wit_2_2.
Axiom proof_of_p091_is_bored_entail_wit_2_3 : p091_is_bored_entail_wit_2_3.
Axiom proof_of_p091_is_bored_entail_wit_2_4 : p091_is_bored_entail_wit_2_4.
Axiom proof_of_p091_is_bored_entail_wit_2_5 : p091_is_bored_entail_wit_2_5.
Axiom proof_of_p091_is_bored_entail_wit_2_6 : p091_is_bored_entail_wit_2_6.
Axiom proof_of_p091_is_bored_entail_wit_2_7 : p091_is_bored_entail_wit_2_7.
Axiom proof_of_p091_is_bored_entail_wit_2_8 : p091_is_bored_entail_wit_2_8.
Axiom proof_of_p091_is_bored_return_wit_1 : p091_is_bored_return_wit_1.
Axiom proof_of_p091_is_bored_partial_solve_wit_1_pure : p091_is_bored_partial_solve_wit_1_pure.
Axiom proof_of_p091_is_bored_partial_solve_wit_1 : p091_is_bored_partial_solve_wit_1.
Axiom proof_of_p091_is_bored_partial_solve_wit_2 : p091_is_bored_partial_solve_wit_2.

End VC_Correct.
