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
Require Import p054_same_chars.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p054_same_chars -----*)

Definition p054_same_chars_safety_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = n1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (retval = n0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "len1" ) )) # Int  |-> retval_2)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "len0" ) )) # Int  |-> retval)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_4 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ False ”
.

Definition p054_same_chars_safety_wit_5 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ False ”
.

Definition p054_same_chars_safety_wit_6 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_7 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p054_same_chars_safety_wit_8 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) ,
  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "i" ) )) # Int  |-> n0)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_9 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_10 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_11 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ False ”
.

Definition p054_same_chars_safety_wit_12 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ False ”
.

Definition p054_same_chars_safety_wit_13 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "found" ) )) # Ptr  |-> retval)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p054_same_chars_safety_wit_14 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p054_same_chars_safety_wit_15 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (i >= n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p054_same_chars_entail_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = n1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (retval = n0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "len1" ) )) # Int  |-> retval_2)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "len0" ) )) # Int  |-> retval)
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix 0 l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_entail_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 ) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix (i + 1 ) l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_entail_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (i >= n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n1)) -> ((Znth (k_4) (l1) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> n0)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_entail_wit_4 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) ,
  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n1)) -> ((Znth (k_4) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix 0 l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_entail_wit_5 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ (retval <> 0) ” 
  &&  “ (char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 ) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix (i + 1 ) l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_return_wit_1 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (i >= n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n1)) -> ((Znth (k_4) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (problem_54_spec l0 l1 1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_return_wit_2 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l1) ((cons (0) (nil)))) 0) l0 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n1)) -> ((Znth (k_4) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (problem_54_spec l0 l1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_return_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((char_in (Znth i (app (l0) ((cons (0) (nil)))) 0) l1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n0)) -> ((Znth (k_3) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n1)) -> ((Znth (k_4) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  “ (problem_54_spec l0 l1 0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_1_pure := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) ,
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  ((( &( "len0" ) )) # Int  |->_)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (((Znth (0) (l0) (0)) <> 0) /\ ((Znth ((n0 - 1 )) (l0) (0)) <> 0)) ”
.

Definition p054_same_chars_partial_solve_wit_1_aux := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) ,
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (((Znth (0) (l0) (0)) <> 0) /\ ((Znth ((n0 - 1 )) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_1 := p054_same_chars_partial_solve_wit_1_pure -> p054_same_chars_partial_solve_wit_1_aux.

Definition p054_same_chars_partial_solve_wit_2_pure := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) ,
  “ (retval = n0) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  ((( &( "len1" ) )) # Int  |->_)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "len0" ) )) # Int  |-> retval)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (((Znth (0) (l1) (0)) <> 0) /\ ((Znth ((n1 - 1 )) (l1) (0)) <> 0)) ”
.

Definition p054_same_chars_partial_solve_wit_2_aux := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (retval: Z) ,
  “ (retval = n0) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (((Znth (0) (l1) (0)) <> 0) /\ ((Znth ((n1 - 1 )) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (retval = n0) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (problem_54_pre l0 l1 ) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (no_zero l0 ) ” 
  &&  “ (no_zero l1 ) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_2 := p054_same_chars_partial_solve_wit_2_pure -> p054_same_chars_partial_solve_wit_2_aux.

Definition p054_same_chars_partial_solve_wit_3 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (((s0_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s0_pre i 0 (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_4_pure := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  ((( &( "found" ) )) # Ptr  |->_)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l0) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ”
.

Definition p054_same_chars_partial_solve_wit_4_aux := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n1)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (i < n0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n0) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_prefix i l0 l1 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_4 := p054_same_chars_partial_solve_wit_4_pure -> p054_same_chars_partial_solve_wit_4_aux.

Definition p054_same_chars_partial_solve_wit_5 := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n1)) -> ((Znth (k_2) (l1) (0)) <> 0)) ”
  &&  (((s1_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s1_pre i 0 (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_6_pure := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  ((( &( "found" ) )) # Ptr  |->_)
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "chr" ) )) # Int  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "len0" ) )) # Int  |-> n0)
  **  ((( &( "len1" ) )) # Int  |-> n1)
  **  ((( &( "s0" ) )) # Ptr  |-> s0_pre)
  **  ((( &( "s1" ) )) # Ptr  |-> s1_pre)
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ”
.

Definition p054_same_chars_partial_solve_wit_6_aux := 
forall (s1_pre: Z) (s0_pre: Z) (n1: Z) (l1: (@list Z)) (n0: Z) (l0: (@list Z)) (i: Z) ,
  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
|--
  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n0)) -> ((Znth (k) (l0) (0)) <> 0)) ” 
  &&  “ (0 <= (n1 + 1 )) ” 
  &&  “ (0 <= (n0 + 1 )) ” 
  &&  “ (i < n1) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n1) ” 
  &&  “ ((Zlength (l0)) = n0) ” 
  &&  “ ((Zlength (l1)) = n1) ” 
  &&  “ (0 <= n0) ” 
  &&  “ (n0 < INT_MAX) ” 
  &&  “ (0 <= n1) ” 
  &&  “ (n1 < INT_MAX) ” 
  &&  “ (ascii_range l0 ) ” 
  &&  “ (ascii_range l1 ) ” 
  &&  “ (same_chars_all l0 l1 ) ” 
  &&  “ (same_chars_prefix i l1 l0 ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n0)) -> ((Znth (k_2) (l0) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n1)) -> ((Znth (k_3) (l1) (0)) <> 0)) ”
  &&  (CharArray.full s0_pre (n0 + 1 ) (app (l0) ((cons (0) (nil)))) )
  **  (CharArray.full s1_pre (n1 + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p054_same_chars_partial_solve_wit_6 := p054_same_chars_partial_solve_wit_6_pure -> p054_same_chars_partial_solve_wit_6_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p054_same_chars_safety_wit_1 : p054_same_chars_safety_wit_1.
Axiom proof_of_p054_same_chars_safety_wit_2 : p054_same_chars_safety_wit_2.
Axiom proof_of_p054_same_chars_safety_wit_3 : p054_same_chars_safety_wit_3.
Axiom proof_of_p054_same_chars_safety_wit_4 : p054_same_chars_safety_wit_4.
Axiom proof_of_p054_same_chars_safety_wit_5 : p054_same_chars_safety_wit_5.
Axiom proof_of_p054_same_chars_safety_wit_6 : p054_same_chars_safety_wit_6.
Axiom proof_of_p054_same_chars_safety_wit_7 : p054_same_chars_safety_wit_7.
Axiom proof_of_p054_same_chars_safety_wit_8 : p054_same_chars_safety_wit_8.
Axiom proof_of_p054_same_chars_safety_wit_9 : p054_same_chars_safety_wit_9.
Axiom proof_of_p054_same_chars_safety_wit_10 : p054_same_chars_safety_wit_10.
Axiom proof_of_p054_same_chars_safety_wit_11 : p054_same_chars_safety_wit_11.
Axiom proof_of_p054_same_chars_safety_wit_12 : p054_same_chars_safety_wit_12.
Axiom proof_of_p054_same_chars_safety_wit_13 : p054_same_chars_safety_wit_13.
Axiom proof_of_p054_same_chars_safety_wit_14 : p054_same_chars_safety_wit_14.
Axiom proof_of_p054_same_chars_safety_wit_15 : p054_same_chars_safety_wit_15.
Axiom proof_of_p054_same_chars_entail_wit_1 : p054_same_chars_entail_wit_1.
Axiom proof_of_p054_same_chars_entail_wit_2 : p054_same_chars_entail_wit_2.
Axiom proof_of_p054_same_chars_entail_wit_3 : p054_same_chars_entail_wit_3.
Axiom proof_of_p054_same_chars_entail_wit_4 : p054_same_chars_entail_wit_4.
Axiom proof_of_p054_same_chars_entail_wit_5 : p054_same_chars_entail_wit_5.
Axiom proof_of_p054_same_chars_return_wit_1 : p054_same_chars_return_wit_1.
Axiom proof_of_p054_same_chars_return_wit_2 : p054_same_chars_return_wit_2.
Axiom proof_of_p054_same_chars_return_wit_3 : p054_same_chars_return_wit_3.
Axiom proof_of_p054_same_chars_partial_solve_wit_1_pure : p054_same_chars_partial_solve_wit_1_pure.
Axiom proof_of_p054_same_chars_partial_solve_wit_1 : p054_same_chars_partial_solve_wit_1.
Axiom proof_of_p054_same_chars_partial_solve_wit_2_pure : p054_same_chars_partial_solve_wit_2_pure.
Axiom proof_of_p054_same_chars_partial_solve_wit_2 : p054_same_chars_partial_solve_wit_2.
Axiom proof_of_p054_same_chars_partial_solve_wit_3 : p054_same_chars_partial_solve_wit_3.
Axiom proof_of_p054_same_chars_partial_solve_wit_4_pure : p054_same_chars_partial_solve_wit_4_pure.
Axiom proof_of_p054_same_chars_partial_solve_wit_4 : p054_same_chars_partial_solve_wit_4.
Axiom proof_of_p054_same_chars_partial_solve_wit_5 : p054_same_chars_partial_solve_wit_5.
Axiom proof_of_p054_same_chars_partial_solve_wit_6_pure : p054_same_chars_partial_solve_wit_6_pure.
Axiom proof_of_p054_same_chars_partial_solve_wit_6 : p054_same_chars_partial_solve_wit_6.

End VC_Correct.
