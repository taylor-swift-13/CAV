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
Require Import ex_hamming_distance.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function ex_hamming_distance -----*)

Definition ex_hamming_distance_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_hamming_distance_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> 0)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_hamming_distance_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_hamming_distance_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_hamming_distance_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((d + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (d + 1 )) ”
.

Definition ex_hamming_distance_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ex_hamming_distance_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "d" ) )) # Int  |-> (d + 1 ))
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ex_hamming_distance_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) ,
  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (0 = (ex_hamming_distance_spec ((sublist (0) (0) (la))) ((sublist (0) (0) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_entail_wit_2_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> (Znth i (app (lb) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ ((d + 1 ) = (ex_hamming_distance_spec ((sublist (0) ((i + 1 )) (la))) ((sublist (0) ((i + 1 )) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_entail_wit_2_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) = (Znth i (app (lb) ((cons (0) (nil)))) 0)) ” 
  &&  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= na) ” 
  &&  “ ((i + 1 ) <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) ((i + 1 )) (la))) ((sublist (0) ((i + 1 )) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (d = (ex_hamming_distance_spec (la) (lb))) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_partial_solve_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_partial_solve_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (((a_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (la) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre i 0 (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
.

Definition ex_hamming_distance_partial_solve_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (nb: Z) (na: Z) (lb: (@list Z)) (la: (@list Z)) (d: Z) (i: Z) ,
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (la) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= na) ” 
  &&  “ (i <= nb) ” 
  &&  “ (na = nb) ” 
  &&  “ (d = (ex_hamming_distance_spec ((sublist (0) (i) (la))) ((sublist (0) (i) (lb))))) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ (0 <= (nb + 1 )) ” 
  &&  “ (0 <= (na + 1 )) ” 
  &&  “ (a_pre <> 0) ” 
  &&  “ (b_pre <> 0) ” 
  &&  “ (0 <= na) ” 
  &&  “ (na < INT_MAX) ” 
  &&  “ (0 <= nb) ” 
  &&  “ (nb < INT_MAX) ” 
  &&  “ ((Zlength (la)) = na) ” 
  &&  “ ((Zlength (lb)) = nb) ” 
  &&  “ (ex_hamming_distance_pre la lb ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < na)) -> ((Znth k la 0) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < nb)) -> ((Znth k_2 lb 0) <> 0)) ”
  &&  (((b_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (lb) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre i 0 (nb + 1 ) (app (lb) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (na + 1 ) (app (la) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_ex_hamming_distance_safety_wit_1 : ex_hamming_distance_safety_wit_1.
Axiom proof_of_ex_hamming_distance_safety_wit_2 : ex_hamming_distance_safety_wit_2.
Axiom proof_of_ex_hamming_distance_safety_wit_3 : ex_hamming_distance_safety_wit_3.
Axiom proof_of_ex_hamming_distance_safety_wit_4 : ex_hamming_distance_safety_wit_4.
Axiom proof_of_ex_hamming_distance_safety_wit_5 : ex_hamming_distance_safety_wit_5.
Axiom proof_of_ex_hamming_distance_safety_wit_6 : ex_hamming_distance_safety_wit_6.
Axiom proof_of_ex_hamming_distance_safety_wit_7 : ex_hamming_distance_safety_wit_7.
Axiom proof_of_ex_hamming_distance_entail_wit_1 : ex_hamming_distance_entail_wit_1.
Axiom proof_of_ex_hamming_distance_entail_wit_2_1 : ex_hamming_distance_entail_wit_2_1.
Axiom proof_of_ex_hamming_distance_entail_wit_2_2 : ex_hamming_distance_entail_wit_2_2.
Axiom proof_of_ex_hamming_distance_return_wit_1 : ex_hamming_distance_return_wit_1.
Axiom proof_of_ex_hamming_distance_partial_solve_wit_1 : ex_hamming_distance_partial_solve_wit_1.
Axiom proof_of_ex_hamming_distance_partial_solve_wit_2 : ex_hamming_distance_partial_solve_wit_2.
Axiom proof_of_ex_hamming_distance_partial_solve_wit_3 : ex_hamming_distance_partial_solve_wit_3.

End VC_Correct.
