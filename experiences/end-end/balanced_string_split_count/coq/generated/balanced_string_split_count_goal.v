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
Require Import balanced_string_split_count.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function balanced_string_split_count -----*)

Definition balanced_string_split_count_safety_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  ((( &( "balance" ) )) # Int  |->_)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "balance" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "balance" ) )) # Int  |-> 0)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> balance)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition balanced_string_split_count_safety_wit_5 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> balance)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_6 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> balance)
|--
  “ (76 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 76) ”
.

Definition balanced_string_split_count_safety_wit_7 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> balance)
|--
  “ ((balance + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (balance + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_8 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> balance)
|--
  “ ((balance - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (balance - 1 )) ”
.

Definition balanced_string_split_count_safety_wit_9 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance - 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_10 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance + 1 ))
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition balanced_string_split_count_safety_wit_11 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance + 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance + 1 ))
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_12 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance - 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance - 1 ))
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_13 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance + 1 ) <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_14 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance - 1 ) <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "balance" ) )) # Int  |-> (balance - 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_15 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance - 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "balance" ) )) # Int  |-> (balance - 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition balanced_string_split_count_safety_wit_16 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance + 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "balance" ) )) # Int  |-> (balance + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition balanced_string_split_count_entail_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((-0) <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (0 = (lr_balance ((sublist (0) (0) (l))))) ” 
  &&  “ ((0 + (balanced_string_split_count_go (0) ((sublist (0) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_entail_wit_2_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance + 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((-(i + 1 )) <= (balance + 1 )) ” 
  &&  “ ((balance + 1 ) <= (i + 1 )) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ ((balance + 1 ) = (lr_balance ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ (((count + 1 ) + (balanced_string_split_count_go ((balance + 1 )) ((sublist ((i + 1 )) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_entail_wit_2_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance - 1 ) = 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((-(i + 1 )) <= (balance - 1 )) ” 
  &&  “ ((balance - 1 ) <= (i + 1 )) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ ((balance - 1 ) = (lr_balance ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ (((count + 1 ) + (balanced_string_split_count_go ((balance - 1 )) ((sublist ((i + 1 )) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_entail_wit_2_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance - 1 ) <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ ((-(i + 1 )) <= (balance - 1 )) ” 
  &&  “ ((balance - 1 ) <= (i + 1 )) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ ((balance - 1 ) = (lr_balance ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go ((balance - 1 )) ((sublist ((i + 1 )) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_entail_wit_2_4 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((balance + 1 ) <> 0) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 76) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ ((-(i + 1 )) <= (balance + 1 )) ” 
  &&  “ ((balance + 1 ) <= (i + 1 )) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ ((balance + 1 ) = (lr_balance ((sublist (0) ((i + 1 )) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go ((balance + 1 )) ((sublist ((i + 1 )) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_entail_wit_3 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance (l))) ” 
  &&  “ (count = (balanced_string_split_count_spec (l))) ”
  &&  ((( &( "i" ) )) # Int  |-> n)
  **  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_return_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) ,
  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance (l))) ” 
  &&  “ (count = (balanced_string_split_count_spec (l))) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (count = (balanced_string_split_count_spec (l))) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_partial_solve_wit_1 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition balanced_string_split_count_partial_solve_wit_2 := 
forall (s_pre: Z) (n: Z) (l: (@list Z)) (balance: Z) (count: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (CharArray.full s_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ ((-i) <= balance) ” 
  &&  “ (balance <= i) ” 
  &&  “ (balanced_string_split_count_pre l ) ” 
  &&  “ (balance = (lr_balance ((sublist (0) (i) (l))))) ” 
  &&  “ ((count + (balanced_string_split_count_go (balance) ((sublist (i) (n) (l)))) ) = (balanced_string_split_count_spec (l))) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth k l 0) <> 0)) ” 
  &&  “ (balanced_string_split_count_pre l ) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_balanced_string_split_count_safety_wit_1 : balanced_string_split_count_safety_wit_1.
Axiom proof_of_balanced_string_split_count_safety_wit_2 : balanced_string_split_count_safety_wit_2.
Axiom proof_of_balanced_string_split_count_safety_wit_3 : balanced_string_split_count_safety_wit_3.
Axiom proof_of_balanced_string_split_count_safety_wit_4 : balanced_string_split_count_safety_wit_4.
Axiom proof_of_balanced_string_split_count_safety_wit_5 : balanced_string_split_count_safety_wit_5.
Axiom proof_of_balanced_string_split_count_safety_wit_6 : balanced_string_split_count_safety_wit_6.
Axiom proof_of_balanced_string_split_count_safety_wit_7 : balanced_string_split_count_safety_wit_7.
Axiom proof_of_balanced_string_split_count_safety_wit_8 : balanced_string_split_count_safety_wit_8.
Axiom proof_of_balanced_string_split_count_safety_wit_9 : balanced_string_split_count_safety_wit_9.
Axiom proof_of_balanced_string_split_count_safety_wit_10 : balanced_string_split_count_safety_wit_10.
Axiom proof_of_balanced_string_split_count_safety_wit_11 : balanced_string_split_count_safety_wit_11.
Axiom proof_of_balanced_string_split_count_safety_wit_12 : balanced_string_split_count_safety_wit_12.
Axiom proof_of_balanced_string_split_count_safety_wit_13 : balanced_string_split_count_safety_wit_13.
Axiom proof_of_balanced_string_split_count_safety_wit_14 : balanced_string_split_count_safety_wit_14.
Axiom proof_of_balanced_string_split_count_safety_wit_15 : balanced_string_split_count_safety_wit_15.
Axiom proof_of_balanced_string_split_count_safety_wit_16 : balanced_string_split_count_safety_wit_16.
Axiom proof_of_balanced_string_split_count_entail_wit_1 : balanced_string_split_count_entail_wit_1.
Axiom proof_of_balanced_string_split_count_entail_wit_2_1 : balanced_string_split_count_entail_wit_2_1.
Axiom proof_of_balanced_string_split_count_entail_wit_2_2 : balanced_string_split_count_entail_wit_2_2.
Axiom proof_of_balanced_string_split_count_entail_wit_2_3 : balanced_string_split_count_entail_wit_2_3.
Axiom proof_of_balanced_string_split_count_entail_wit_2_4 : balanced_string_split_count_entail_wit_2_4.
Axiom proof_of_balanced_string_split_count_entail_wit_3 : balanced_string_split_count_entail_wit_3.
Axiom proof_of_balanced_string_split_count_return_wit_1 : balanced_string_split_count_return_wit_1.
Axiom proof_of_balanced_string_split_count_partial_solve_wit_1 : balanced_string_split_count_partial_solve_wit_1.
Axiom proof_of_balanced_string_split_count_partial_solve_wit_2 : balanced_string_split_count_partial_solve_wit_2.

End VC_Correct.
