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
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function p011_string_xor -----*)

Definition p011_string_xor_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition p011_string_xor_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p011_string_xor_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((retval + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval + 1 )) ”
.

Definition p011_string_xor_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p011_string_xor_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (l: (@list Z)) (retval_3: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full retval_3 (retval_2 + 1 ) l )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p011_string_xor_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) (l: (@list Z)) (retval_3: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full retval_3 (retval + 1 ) l )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p011_string_xor_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p011_string_xor_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p011_string_xor_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition p011_string_xor_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (49 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 49) ”
.

Definition p011_string_xor_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p011_string_xor_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p011_string_xor_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p011_string_xor_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "output" ) )) # Ptr  |-> output)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p011_string_xor_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p011_string_xor_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  ((( &( "output" ) )) # Ptr  |-> output)
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p011_string_xor_entail_wit_1_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n1" ) )) # Int  |-> retval)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval_2 >= retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) ))
.

Definition p011_string_xor_entail_wit_1_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  (“ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval < retval) ” 
  &&  “ (retval = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= retval_2) ” 
  &&  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval >= retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) ))
.

Definition p011_string_xor_entail_wit_2_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval_3: Z) (l: (@list Z)) (retval: Z) ,
  “ (0 <= retval_2) ” 
  &&  “ (retval_2 <= retval_2) ” 
  &&  “ (retval_2 <= retval_3) ” 
  &&  “ (retval_2 < retval_3) ” 
  &&  “ (retval_3 = nb) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth (k_4) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (l2) (0)) <> 0)) ”
  &&  (CharArray.full retval (retval_2 + 1 ) l )
  **  ((( &( "n" ) )) # Int  |-> retval_2)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (na + 1 ) ))
.

Definition p011_string_xor_entail_wit_2_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval_3: Z) (l: (@list Z)) (retval: Z) ,
  “ (0 <= retval_3) ” 
  &&  “ (retval_3 <= retval_2) ” 
  &&  “ (retval_3 <= retval_3) ” 
  &&  “ (retval_2 >= retval_3) ” 
  &&  “ (retval_3 = nb) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < na)) -> ((Znth (k_4) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (l2) (0)) <> 0)) ”
  &&  (CharArray.full retval (retval_3 + 1 ) l )
  **  ((( &( "n" ) )) # Int  |-> retval_3)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval_3)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = 0) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < 0)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n1" ) )) # Int  |-> na)
  **  ((( &( "n2" ) )) # Int  |-> nb)
  **  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full retval 0 out_l )
  **  (CharArray.undef_seg retval 0 (na + 1 ) ))
.

Definition p011_string_xor_entail_wit_3_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> nb)
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition p011_string_xor_entail_wit_3_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (48) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> na)
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition p011_string_xor_entail_wit_3_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> nb)
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition p011_string_xor_entail_wit_3_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (49) (nil)))) )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> na)
|--
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> nb)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (nb + 1 ) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = (i + 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < (i + 1 ))) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  ((( &( "n" ) )) # Int  |-> na)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (i + 1 ) out_l )
  **  (CharArray.undef_seg output (i + 1 ) (na + 1 ) ))
.

Definition p011_string_xor_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (i >= na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < i)) -> ((((Znth (k_7) (l1) (0)) = (Znth (k_7) (l2) (0))) /\ ((Znth (k_7) (out_l_2) (0)) = 48)) \/ (((Znth (k_7) (l1) (0)) <> (Znth (k_7) (l2) (0))) /\ ((Znth (k_7) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output (na + 1 ) (na + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z))  (n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (out_l) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (n = nb) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((((Znth (k_4) (l1) (0)) = (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 48)) \/ (((Znth (k_4) (l1) (0)) <> (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
  ||
  (EX (out_l: (@list Z))  (n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (out_l) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (n = na) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((((Znth (k_4) (l1) (0)) = (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 48)) \/ (((Znth (k_4) (l1) (0)) <> (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
.

Definition p011_string_xor_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l_2: (@list Z)) (i: Z) ,
  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (i >= nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < na)) -> ((Znth (k_5) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_6: Z) , (((0 <= k_6) /\ (k_6 < nb)) -> ((Znth (k_6) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l_2)) = i) ” 
  &&  “ forall (k_7: Z) , (((0 <= k_7) /\ (k_7 < i)) -> ((((Znth (k_7) (l1) (0)) = (Znth (k_7) (l2) (0))) /\ ((Znth (k_7) (out_l_2) (0)) = 48)) \/ (((Znth (k_7) (l1) (0)) <> (Znth (k_7) (l2) (0))) /\ ((Znth (k_7) (out_l_2) (0)) = 49)))) ”
  &&  (CharArray.full output (i + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg output (nb + 1 ) (nb + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  (EX (out_l: (@list Z))  (n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (out_l) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (n = nb) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((((Znth (k_4) (l1) (0)) = (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 48)) \/ (((Znth (k_4) (l1) (0)) <> (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
  ||
  (EX (out_l: (@list Z))  (n: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (out_l) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (n = na) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((((Znth (k_4) (l1) (0)) = (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 48)) \/ (((Znth (k_4) (l1) (0)) <> (Znth (k_4) (l2) (0))) /\ ((Znth (k_4) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output (n + 1 ) (app (out_l) ((cons (0) (nil)))) ))
.

Definition p011_string_xor_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n1" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ”
.

Definition p011_string_xor_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) ,
  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
.

Definition p011_string_xor_partial_solve_wit_1 := p011_string_xor_partial_solve_wit_1_pure -> p011_string_xor_partial_solve_wit_1_aux.

Definition p011_string_xor_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) ,
  “ (retval = na) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (l2) (0)) <> 0)) ”
  &&  ((( &( "n2" ) )) # Int  |->_)
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ”
.

Definition p011_string_xor_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) ,
  “ (retval = na) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (l2) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
|--
  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < na)) -> ((Znth (k_3) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < nb)) -> ((Znth (k_4) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p011_string_xor_partial_solve_wit_2 := p011_string_xor_partial_solve_wit_2_pure -> p011_string_xor_partial_solve_wit_2_aux.

Definition p011_string_xor_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval)
  **  ((( &( "n2" ) )) # Int  |-> retval_2)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition p011_string_xor_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval < retval_2) ” 
  &&  “ (retval_2 = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p011_string_xor_partial_solve_wit_3 := p011_string_xor_partial_solve_wit_3_pure -> p011_string_xor_partial_solve_wit_3_aux.

Definition p011_string_xor_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "n1" ) )) # Int  |-> retval_2)
  **  ((( &( "n2" ) )) # Int  |-> retval)
  **  ((( &( "output" ) )) # Ptr  |->_)
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((retval + 1 ) > 0) ”
.

Definition p011_string_xor_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (retval_2: Z) (retval: Z) ,
  “ (0 <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
|--
  “ ((retval + 1 ) > 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval <= retval_2) ” 
  &&  “ (retval <= retval) ” 
  &&  “ (retval_2 >= retval) ” 
  &&  “ (retval = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < nb)) -> ((Znth (k) (l2) (0)) <> 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (retval_2 = na) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < na)) -> ((Znth (k_2) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < nb)) -> ((Znth (k_3) (l2) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
.

Definition p011_string_xor_partial_solve_wit_4 := p011_string_xor_partial_solve_wit_4_pure -> p011_string_xor_partial_solve_wit_4_aux.

Definition p011_string_xor_partial_solve_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
.

Definition p011_string_xor_partial_solve_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l1) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
.

Definition p011_string_xor_partial_solve_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
.

Definition p011_string_xor_partial_solve_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l2) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
.

Definition p011_string_xor_partial_solve_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition p011_string_xor_partial_solve_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) = (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition p011_string_xor_partial_solve_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (nb + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition p011_string_xor_partial_solve_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ ((Znth i (app (l1) ((cons (0) (nil)))) 0) <> (Znth i (app (l2) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (i < na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output i i (na + 1 ) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition p011_string_xor_partial_solve_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (na + 1 ) )
|--
  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (i >= na) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (na <= nb) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (na <= na) ” 
  &&  “ (na <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (na * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output na i (na + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Definition p011_string_xor_partial_solve_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (l2: (@list Z)) (l1: (@list Z)) (output: Z) (out_l: (@list Z)) (i: Z) ,
  “ (i >= nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
  **  (CharArray.undef_seg output i (nb + 1 ) )
|--
  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (i >= nb) ” 
  &&  “ ((Zlength (l1)) = na) ” 
  &&  “ ((Zlength (l2)) = nb) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth (k) (l1) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth (k_2) (l2) (0)) <> 0)) ” 
  &&  “ (nb < na) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= nb) ” 
  &&  “ (nb <= na) ” 
  &&  “ (nb <= nb) ” 
  &&  “ ((Zlength (out_l)) = i) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((((Znth (k_3) (l1) (0)) = (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 48)) \/ (((Znth (k_3) (l1) (0)) <> (Znth (k_3) (l2) (0))) /\ ((Znth (k_3) (out_l) (0)) = 49)))) ”
  &&  (((output + (nb * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i output nb i (nb + 1 ) )
  **  (CharArray.full a_pre (na + 1 ) (app (l1) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (l2) ((cons (0) (nil)))) )
  **  (CharArray.full output i out_l )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p011_string_xor_safety_wit_1 : p011_string_xor_safety_wit_1.
Axiom proof_of_p011_string_xor_safety_wit_2 : p011_string_xor_safety_wit_2.
Axiom proof_of_p011_string_xor_safety_wit_3 : p011_string_xor_safety_wit_3.
Axiom proof_of_p011_string_xor_safety_wit_4 : p011_string_xor_safety_wit_4.
Axiom proof_of_p011_string_xor_safety_wit_5 : p011_string_xor_safety_wit_5.
Axiom proof_of_p011_string_xor_safety_wit_6 : p011_string_xor_safety_wit_6.
Axiom proof_of_p011_string_xor_safety_wit_7 : p011_string_xor_safety_wit_7.
Axiom proof_of_p011_string_xor_safety_wit_8 : p011_string_xor_safety_wit_8.
Axiom proof_of_p011_string_xor_safety_wit_9 : p011_string_xor_safety_wit_9.
Axiom proof_of_p011_string_xor_safety_wit_10 : p011_string_xor_safety_wit_10.
Axiom proof_of_p011_string_xor_safety_wit_11 : p011_string_xor_safety_wit_11.
Axiom proof_of_p011_string_xor_safety_wit_12 : p011_string_xor_safety_wit_12.
Axiom proof_of_p011_string_xor_safety_wit_13 : p011_string_xor_safety_wit_13.
Axiom proof_of_p011_string_xor_safety_wit_14 : p011_string_xor_safety_wit_14.
Axiom proof_of_p011_string_xor_safety_wit_15 : p011_string_xor_safety_wit_15.
Axiom proof_of_p011_string_xor_safety_wit_16 : p011_string_xor_safety_wit_16.
Axiom proof_of_p011_string_xor_entail_wit_1_1 : p011_string_xor_entail_wit_1_1.
Axiom proof_of_p011_string_xor_entail_wit_1_2 : p011_string_xor_entail_wit_1_2.
Axiom proof_of_p011_string_xor_entail_wit_2_1 : p011_string_xor_entail_wit_2_1.
Axiom proof_of_p011_string_xor_entail_wit_2_2 : p011_string_xor_entail_wit_2_2.
Axiom proof_of_p011_string_xor_entail_wit_3_1 : p011_string_xor_entail_wit_3_1.
Axiom proof_of_p011_string_xor_entail_wit_3_2 : p011_string_xor_entail_wit_3_2.
Axiom proof_of_p011_string_xor_entail_wit_3_3 : p011_string_xor_entail_wit_3_3.
Axiom proof_of_p011_string_xor_entail_wit_3_4 : p011_string_xor_entail_wit_3_4.
Axiom proof_of_p011_string_xor_return_wit_1 : p011_string_xor_return_wit_1.
Axiom proof_of_p011_string_xor_return_wit_2 : p011_string_xor_return_wit_2.
Axiom proof_of_p011_string_xor_partial_solve_wit_1_pure : p011_string_xor_partial_solve_wit_1_pure.
Axiom proof_of_p011_string_xor_partial_solve_wit_1 : p011_string_xor_partial_solve_wit_1.
Axiom proof_of_p011_string_xor_partial_solve_wit_2_pure : p011_string_xor_partial_solve_wit_2_pure.
Axiom proof_of_p011_string_xor_partial_solve_wit_2 : p011_string_xor_partial_solve_wit_2.
Axiom proof_of_p011_string_xor_partial_solve_wit_3_pure : p011_string_xor_partial_solve_wit_3_pure.
Axiom proof_of_p011_string_xor_partial_solve_wit_3 : p011_string_xor_partial_solve_wit_3.
Axiom proof_of_p011_string_xor_partial_solve_wit_4_pure : p011_string_xor_partial_solve_wit_4_pure.
Axiom proof_of_p011_string_xor_partial_solve_wit_4 : p011_string_xor_partial_solve_wit_4.
Axiom proof_of_p011_string_xor_partial_solve_wit_5 : p011_string_xor_partial_solve_wit_5.
Axiom proof_of_p011_string_xor_partial_solve_wit_6 : p011_string_xor_partial_solve_wit_6.
Axiom proof_of_p011_string_xor_partial_solve_wit_7 : p011_string_xor_partial_solve_wit_7.
Axiom proof_of_p011_string_xor_partial_solve_wit_8 : p011_string_xor_partial_solve_wit_8.
Axiom proof_of_p011_string_xor_partial_solve_wit_9 : p011_string_xor_partial_solve_wit_9.
Axiom proof_of_p011_string_xor_partial_solve_wit_10 : p011_string_xor_partial_solve_wit_10.
Axiom proof_of_p011_string_xor_partial_solve_wit_11 : p011_string_xor_partial_solve_wit_11.
Axiom proof_of_p011_string_xor_partial_solve_wit_12 : p011_string_xor_partial_solve_wit_12.
Axiom proof_of_p011_string_xor_partial_solve_wit_13 : p011_string_xor_partial_solve_wit_13.
Axiom proof_of_p011_string_xor_partial_solve_wit_14 : p011_string_xor_partial_solve_wit_14.

End VC_Correct.
