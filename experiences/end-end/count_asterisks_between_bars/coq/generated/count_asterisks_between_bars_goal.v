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
Require Import count_asterisks_between_bars.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function count_asterisks_between_bars -----*)

Definition count_asterisks_between_bars_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "inside" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_asterisks_between_bars_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "inside" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_asterisks_between_bars_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "inside" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_asterisks_between_bars_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_asterisks_between_bars_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_asterisks_between_bars_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ (124 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 124) ”
.

Definition count_asterisks_between_bars_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ (42 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 42) ”
.

Definition count_asterisks_between_bars_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (inside <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition count_asterisks_between_bars_safety_wit_9 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (inside = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_asterisks_between_bars_safety_wit_10 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_asterisks_between_bars_safety_wit_11 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (inside <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "inside" ) )) # Int  |-> inside)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_asterisks_between_bars_safety_wit_12 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (inside = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> 1)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_asterisks_between_bars_safety_wit_13 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (inside <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "inside" ) )) # Int  |-> 0)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition count_asterisks_between_bars_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((0 + (count_asterisks_between_bars_go (0) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ (inside <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (0) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ (inside = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (1) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_2_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ (inside <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ (((count + 1 ) + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_2_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_2_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ (inside = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 42) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = (i + 1 )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix_2: (@list Z)) (suffix_2: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) ” 
  &&  “ (l = (app (prefix_2) (suffix_2))) ” 
  &&  “ ((Zlength (prefix_2)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix_2)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth k_2 l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  EX (prefix: (@list Z))  (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ ((Zlength (prefix)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (prefix: (@list Z)) (suffix: (@list Z)) (count: Z) (inside: Z) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ ((Zlength (prefix)) = n) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= n) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (count = (count_asterisks_between_bars_spec (l))) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition count_asterisks_between_bars_partial_solve_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (inside: Z) (count: Z) (i: Z) (prefix: (@list Z)) (suffix: (@list Z)) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 124) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (l = (app (prefix) (suffix))) ” 
  &&  “ ((Zlength (prefix)) = i) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (0 <= inside) ” 
  &&  “ (inside <= 1) ” 
  &&  “ ((count + (count_asterisks_between_bars_go (inside) (suffix)) ) = (count_asterisks_between_bars_spec (l))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_count_asterisks_between_bars_safety_wit_1 : count_asterisks_between_bars_safety_wit_1.
Axiom proof_of_count_asterisks_between_bars_safety_wit_2 : count_asterisks_between_bars_safety_wit_2.
Axiom proof_of_count_asterisks_between_bars_safety_wit_3 : count_asterisks_between_bars_safety_wit_3.
Axiom proof_of_count_asterisks_between_bars_safety_wit_4 : count_asterisks_between_bars_safety_wit_4.
Axiom proof_of_count_asterisks_between_bars_safety_wit_5 : count_asterisks_between_bars_safety_wit_5.
Axiom proof_of_count_asterisks_between_bars_safety_wit_6 : count_asterisks_between_bars_safety_wit_6.
Axiom proof_of_count_asterisks_between_bars_safety_wit_7 : count_asterisks_between_bars_safety_wit_7.
Axiom proof_of_count_asterisks_between_bars_safety_wit_8 : count_asterisks_between_bars_safety_wit_8.
Axiom proof_of_count_asterisks_between_bars_safety_wit_9 : count_asterisks_between_bars_safety_wit_9.
Axiom proof_of_count_asterisks_between_bars_safety_wit_10 : count_asterisks_between_bars_safety_wit_10.
Axiom proof_of_count_asterisks_between_bars_safety_wit_11 : count_asterisks_between_bars_safety_wit_11.
Axiom proof_of_count_asterisks_between_bars_safety_wit_12 : count_asterisks_between_bars_safety_wit_12.
Axiom proof_of_count_asterisks_between_bars_safety_wit_13 : count_asterisks_between_bars_safety_wit_13.
Axiom proof_of_count_asterisks_between_bars_entail_wit_1 : count_asterisks_between_bars_entail_wit_1.
Axiom proof_of_count_asterisks_between_bars_entail_wit_2_1 : count_asterisks_between_bars_entail_wit_2_1.
Axiom proof_of_count_asterisks_between_bars_entail_wit_2_2 : count_asterisks_between_bars_entail_wit_2_2.
Axiom proof_of_count_asterisks_between_bars_entail_wit_2_3 : count_asterisks_between_bars_entail_wit_2_3.
Axiom proof_of_count_asterisks_between_bars_entail_wit_2_4 : count_asterisks_between_bars_entail_wit_2_4.
Axiom proof_of_count_asterisks_between_bars_entail_wit_2_5 : count_asterisks_between_bars_entail_wit_2_5.
Axiom proof_of_count_asterisks_between_bars_entail_wit_3 : count_asterisks_between_bars_entail_wit_3.
Axiom proof_of_count_asterisks_between_bars_return_wit_1 : count_asterisks_between_bars_return_wit_1.
Axiom proof_of_count_asterisks_between_bars_partial_solve_wit_1 : count_asterisks_between_bars_partial_solve_wit_1.
Axiom proof_of_count_asterisks_between_bars_partial_solve_wit_2 : count_asterisks_between_bars_partial_solve_wit_2.
Axiom proof_of_count_asterisks_between_bars_partial_solve_wit_3 : count_asterisks_between_bars_partial_solve_wit_3.

End VC_Correct.
