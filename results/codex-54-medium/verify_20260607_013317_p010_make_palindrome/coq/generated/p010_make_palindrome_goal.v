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
Require Import p010_make_palindrome.
Require Import string_bridge.
Local Open Scope sac.
From SimpleC.EE.CAV Require Import char_array_strategy_goal.
From SimpleC.EE.CAV Require Import char_array_strategy_proof.

(*----- Function is_pal_suffix -----*)

Definition is_pal_suffix_safety_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((n_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - 1 )) ”
.

Definition is_pal_suffix_safety_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_pal_suffix_safety_wit_3 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  “ (start_pre = n_pre) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |-> (n_pre - 1 ))
  **  ((( &( "i" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_pal_suffix_safety_wit_4 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_pal_suffix_safety_wit_5 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition is_pal_suffix_safety_wit_6 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_pal_suffix_safety_wit_7 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition is_pal_suffix_safety_wit_8 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_pal_suffix_safety_wit_9 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i >= j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "start" ) )) # Int  |-> start_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "s" ) )) # Ptr  |-> s_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition is_pal_suffix_entail_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  “ (start_pre <> n_pre) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= start_pre) ” 
  &&  “ (start_pre <= ((n_pre - 1 ) + 1 )) ” 
  &&  “ ((n_pre - 1 ) < n_pre) ” 
  &&  “ ((start_pre + (n_pre - 1 ) ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (start_pre - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_entail_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= ((j - 1 ) + 1 )) ” 
  &&  “ ((j - 1 ) < n_pre) ” 
  &&  “ (((i + 1 ) + (j - 1 ) ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < ((i + 1 ) - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_return_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i >= j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i - start_pre ))) -> ((Znth ((start_pre + k_2 )) (l) (0)) = (Znth (((n_pre - 1 ) - k_2 )) (l) (0)))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pal_suffix start_pre l ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((pal_suffix start_pre l )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_return_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i - start_pre ))) -> ((Znth ((start_pre + k_2 )) (l) (0)) = (Znth (((n_pre - 1 ) - k_2 )) (l) (0)))) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 1) ” 
  &&  “ (pal_suffix start_pre l ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 = 0) ” 
  &&  “ ~((pal_suffix start_pre l )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_return_wit_3 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) ,
  “ (start_pre = n_pre) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (1 = 1) ” 
  &&  “ (pal_suffix start_pre l ) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (1 = 0) ” 
  &&  “ ~((pal_suffix start_pre l )) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition is_pal_suffix_partial_solve_wit_1 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((s_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre i 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition is_pal_suffix_partial_solve_wit_2 := 
forall (n_pre: Z) (start_pre: Z) (s_pre: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full s_pre (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < j) ” 
  &&  “ (0 <= start_pre) ” 
  &&  “ (start_pre <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n_pre) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (start_pre <= i) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n_pre) ” 
  &&  “ ((i + j ) = ((start_pre + n_pre ) - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < (i - start_pre ))) -> ((Znth ((start_pre + k )) (l) (0)) = (Znth (((n_pre - 1 ) - k )) (l) (0)))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n_pre)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (((s_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i s_pre j 0 (n_pre + 1 ) (app (l) ((cons (0) (nil)))) )
.

(*----- Function p010_make_palindrome -----*)

Definition p010_make_palindrome_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "best" ) )) # Int  |-> retval)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p010_make_palindrome_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best <> len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((pal_suffix i l )) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p010_make_palindrome_safety_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (pal_suffix i l ) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p010_make_palindrome_safety_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((pal_suffix i l )) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (pal_suffix i l ) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best <> len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((pal_suffix i l )) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_10 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (pal_suffix i l ) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_11 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_12 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best <> len) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p010_make_palindrome_safety_wit_13 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p010_make_palindrome_safety_wit_14 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "out_len" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((len + best ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + best )) ”
.

Definition p010_make_palindrome_safety_wit_15 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((len + best ) + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_16 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p010_make_palindrome_safety_wit_17 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval ((len + best ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p010_make_palindrome_safety_wit_18 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_19 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (i >= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "k" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i (sublist (0) (i) (l)) )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p010_make_palindrome_safety_wit_20 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((len + k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (len + k )) ”
.

Definition p010_make_palindrome_safety_wit_21 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((best - 1 ) - k ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((best - 1 ) - k )) ”
.

Definition p010_make_palindrome_safety_wit_22 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((best - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (best - 1 )) ”
.

Definition p010_make_palindrome_safety_wit_23 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p010_make_palindrome_safety_wit_24 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= (len + k )) ” 
  &&  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out ((len + k ) + 1 ) (app ((app (l) ((rev ((sublist ((best - k )) (best) (l))))))) ((cons ((Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out ((len + k ) + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition p010_make_palindrome_safety_wit_25 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (out_len: Z) (i: Z) (k: Z) (out: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (k = best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "out_len" ) )) # Int  |-> out_len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (len + best ) (app (l) ((rev ((sublist (0) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + best ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p010_make_palindrome_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < len)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
|--
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (retval = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < 0)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < 0) ” 
  &&  “ (first_pal_suffix retval l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |-> len)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p010_make_palindrome_entail_wit_3_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (pal_suffix i l ) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (i = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < (i + 1 ))) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < (i + 1 )) ” 
  &&  “ (first_pal_suffix i l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p010_make_palindrome_entail_wit_3_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((pal_suffix i l )) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < (i + 1 ))) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < (i + 1 )) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p010_make_palindrome_entail_wit_3_3 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best <> len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < (i + 1 ))) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < (i + 1 )) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) ))
.

Definition p010_make_palindrome_entail_wit_4_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ (first_pal_suffix 0 l ) ” 
  &&  “ ((len + 0 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + 0 )) ” 
  &&  “ (((len + 0 ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + 0 ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_4_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best <> len) ” 
  &&  “ (i >= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best < i) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.undef_full retval ((len + best ) + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full retval 0 (sublist (0) (0) (l)) )
  **  (CharArray.undef_seg retval 0 ((len + best ) + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (i + 1 ) (app ((sublist (0) (i) (l))) ((cons ((Znth i (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (i + 1 ) (sublist (0) ((i + 1 )) (l)) )
  **  (CharArray.undef_seg out (i + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (i >= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full out i (sublist (0) (i) (l)) )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + 0 ) (app (l) ((rev ((sublist ((best - 0 )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + 0 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= (len + k )) ” 
  &&  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out ((len + k ) + 1 ) (app ((app (l) ((rev ((sublist ((best - k )) (best) (l))))))) ((cons ((Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0)) (nil)))) )
  **  (CharArray.undef_seg out ((len + k ) + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= (k + 1 )) ” 
  &&  “ ((k + 1 ) <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + (k + 1 ) ) (app (l) ((rev ((sublist ((best - (k + 1 ) )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + (k + 1 ) ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_entail_wit_9 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k >= best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j_2: Z) , (((0 <= j_2) /\ (j_2 < len)) -> ((Znth (j_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (k = best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + best ) (app (l) ((rev ((sublist (0) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + best ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (out_len: Z) (i: Z) (k_3: Z) (out: Z) ,
  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= (len + best )) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (k_3 = best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out ((len + best ) + 1 ) (app ((app (l) ((rev ((sublist (0) (best) (l))))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (out_len + 1 ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z)) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (Zlength (out_l)))) -> ((Znth (k_2) (out_l) (0)) <> 0)) ” 
  &&  “ (problem_10_spec l out_l ) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out ((Zlength (out_l)) + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_partial_solve_wit_1_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (len < INT_MAX) ”
.

Definition p010_make_palindrome_partial_solve_wit_1_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_partial_solve_wit_1 := p010_make_palindrome_partial_solve_wit_1_pure -> p010_make_palindrome_partial_solve_wit_1_aux.

Definition p010_make_palindrome_partial_solve_wit_2_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (len < INT_MAX) ”
.

Definition p010_make_palindrome_partial_solve_wit_2_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (0 <= len) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ (best = len) ” 
  &&  “ (i < len) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ (best = len) ” 
  &&  “ forall (t: Z) , (((0 <= t) /\ (t < i)) -> ~((pal_suffix t l ))) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_partial_solve_wit_2 := p010_make_palindrome_partial_solve_wit_2_pure -> p010_make_palindrome_partial_solve_wit_2_aux.

Definition p010_make_palindrome_partial_solve_wit_3_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "out_len" ) )) # Int  |-> (len + best ))
  **  ((( &( "n" ) )) # Int  |-> len)
  **  ((( &( "best" ) )) # Int  |-> best)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((len + best ) + 1 ) > 0) ”
.

Definition p010_make_palindrome_partial_solve_wit_3_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (i: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (((len + best ) + 1 ) > 0) ” 
  &&  “ (0 <= (len + 1 )) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (i = len) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p010_make_palindrome_partial_solve_wit_3 := p010_make_palindrome_partial_solve_wit_3_pure -> p010_make_palindrome_partial_solve_wit_3_aux.

Definition p010_make_palindrome_partial_solve_wit_4 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full out i (sublist (0) (i) (l)) )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (((str_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre i 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i (sublist (0) (i) (l)) )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
.

Definition p010_make_palindrome_partial_solve_wit_5 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i (sublist (0) (i) (l)) )
  **  (CharArray.undef_seg out i (out_len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (i < len) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out i (sublist (0) (i) (l)) )
.

Definition p010_make_palindrome_partial_solve_wit_6 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (len + k )) ” 
  &&  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (((str_pre + (((best - 1 ) - k ) * sizeof(CHAR) ) )) # Char  |-> (Znth ((best - 1 ) - k ) (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str_pre ((best - 1 ) - k ) 0 (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
.

Definition p010_make_palindrome_partial_solve_wit_7 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (out: Z) (k: Z) (i: Z) (out_len: Z) (best: Z) ,
  “ (0 <= (len + k )) ” 
  &&  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + k ) (out_len + 1 ) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= (len + k )) ” 
  &&  “ (k < best) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (0 <= k) ” 
  &&  “ (k <= best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (((out + ((len + k ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (len + k ) (len + k ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  (CharArray.full out (len + k ) (app (l) ((rev ((sublist ((best - k )) (best) (l)))))) )
.

Definition p010_make_palindrome_partial_solve_wit_8 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (best: Z) (out_len: Z) (i: Z) (k: Z) (out: Z) ,
  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (k = best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (CharArray.full out (len + best ) (app (l) ((rev ((sublist (0) (best) (l)))))) )
  **  (CharArray.undef_seg out (len + best ) (out_len + 1 ) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (len + 1 )) ” 
  &&  “ (0 <= (len + best )) ” 
  &&  “ (len < (INT_MAX ÷ 2 )) ” 
  &&  “ (0 <= best) ” 
  &&  “ (best <= len) ” 
  &&  “ (first_pal_suffix best l ) ” 
  &&  “ (out_len = (len + best )) ” 
  &&  “ ((len + best ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= (len + best )) ” 
  &&  “ (((len + best ) + 1 ) <= INT_MAX) ” 
  &&  “ (INT_MIN <= ((len + best ) + 1 )) ” 
  &&  “ (problem_10_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (i = len) ” 
  &&  “ (k = best) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < len)) -> ((Znth (j) (l) (0)) <> 0)) ”
  &&  (((out + (out_len * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out out_len (len + best ) (out_len + 1 ) )
  **  (CharArray.full out (len + best ) (app (l) ((rev ((sublist (0) (best) (l)))))) )
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_is_pal_suffix_safety_wit_1 : is_pal_suffix_safety_wit_1.
Axiom proof_of_is_pal_suffix_safety_wit_2 : is_pal_suffix_safety_wit_2.
Axiom proof_of_is_pal_suffix_safety_wit_3 : is_pal_suffix_safety_wit_3.
Axiom proof_of_is_pal_suffix_safety_wit_4 : is_pal_suffix_safety_wit_4.
Axiom proof_of_is_pal_suffix_safety_wit_5 : is_pal_suffix_safety_wit_5.
Axiom proof_of_is_pal_suffix_safety_wit_6 : is_pal_suffix_safety_wit_6.
Axiom proof_of_is_pal_suffix_safety_wit_7 : is_pal_suffix_safety_wit_7.
Axiom proof_of_is_pal_suffix_safety_wit_8 : is_pal_suffix_safety_wit_8.
Axiom proof_of_is_pal_suffix_safety_wit_9 : is_pal_suffix_safety_wit_9.
Axiom proof_of_is_pal_suffix_entail_wit_1 : is_pal_suffix_entail_wit_1.
Axiom proof_of_is_pal_suffix_entail_wit_2 : is_pal_suffix_entail_wit_2.
Axiom proof_of_is_pal_suffix_return_wit_1 : is_pal_suffix_return_wit_1.
Axiom proof_of_is_pal_suffix_return_wit_2 : is_pal_suffix_return_wit_2.
Axiom proof_of_is_pal_suffix_return_wit_3 : is_pal_suffix_return_wit_3.
Axiom proof_of_is_pal_suffix_partial_solve_wit_1 : is_pal_suffix_partial_solve_wit_1.
Axiom proof_of_is_pal_suffix_partial_solve_wit_2 : is_pal_suffix_partial_solve_wit_2.
Axiom proof_of_p010_make_palindrome_safety_wit_1 : p010_make_palindrome_safety_wit_1.
Axiom proof_of_p010_make_palindrome_safety_wit_2 : p010_make_palindrome_safety_wit_2.
Axiom proof_of_p010_make_palindrome_safety_wit_3 : p010_make_palindrome_safety_wit_3.
Axiom proof_of_p010_make_palindrome_safety_wit_4 : p010_make_palindrome_safety_wit_4.
Axiom proof_of_p010_make_palindrome_safety_wit_5 : p010_make_palindrome_safety_wit_5.
Axiom proof_of_p010_make_palindrome_safety_wit_6 : p010_make_palindrome_safety_wit_6.
Axiom proof_of_p010_make_palindrome_safety_wit_7 : p010_make_palindrome_safety_wit_7.
Axiom proof_of_p010_make_palindrome_safety_wit_8 : p010_make_palindrome_safety_wit_8.
Axiom proof_of_p010_make_palindrome_safety_wit_9 : p010_make_palindrome_safety_wit_9.
Axiom proof_of_p010_make_palindrome_safety_wit_10 : p010_make_palindrome_safety_wit_10.
Axiom proof_of_p010_make_palindrome_safety_wit_11 : p010_make_palindrome_safety_wit_11.
Axiom proof_of_p010_make_palindrome_safety_wit_12 : p010_make_palindrome_safety_wit_12.
Axiom proof_of_p010_make_palindrome_safety_wit_13 : p010_make_palindrome_safety_wit_13.
Axiom proof_of_p010_make_palindrome_safety_wit_14 : p010_make_palindrome_safety_wit_14.
Axiom proof_of_p010_make_palindrome_safety_wit_15 : p010_make_palindrome_safety_wit_15.
Axiom proof_of_p010_make_palindrome_safety_wit_16 : p010_make_palindrome_safety_wit_16.
Axiom proof_of_p010_make_palindrome_safety_wit_17 : p010_make_palindrome_safety_wit_17.
Axiom proof_of_p010_make_palindrome_safety_wit_18 : p010_make_palindrome_safety_wit_18.
Axiom proof_of_p010_make_palindrome_safety_wit_19 : p010_make_palindrome_safety_wit_19.
Axiom proof_of_p010_make_palindrome_safety_wit_20 : p010_make_palindrome_safety_wit_20.
Axiom proof_of_p010_make_palindrome_safety_wit_21 : p010_make_palindrome_safety_wit_21.
Axiom proof_of_p010_make_palindrome_safety_wit_22 : p010_make_palindrome_safety_wit_22.
Axiom proof_of_p010_make_palindrome_safety_wit_23 : p010_make_palindrome_safety_wit_23.
Axiom proof_of_p010_make_palindrome_safety_wit_24 : p010_make_palindrome_safety_wit_24.
Axiom proof_of_p010_make_palindrome_safety_wit_25 : p010_make_palindrome_safety_wit_25.
Axiom proof_of_p010_make_palindrome_entail_wit_1 : p010_make_palindrome_entail_wit_1.
Axiom proof_of_p010_make_palindrome_entail_wit_2 : p010_make_palindrome_entail_wit_2.
Axiom proof_of_p010_make_palindrome_entail_wit_3_1 : p010_make_palindrome_entail_wit_3_1.
Axiom proof_of_p010_make_palindrome_entail_wit_3_2 : p010_make_palindrome_entail_wit_3_2.
Axiom proof_of_p010_make_palindrome_entail_wit_3_3 : p010_make_palindrome_entail_wit_3_3.
Axiom proof_of_p010_make_palindrome_entail_wit_4_1 : p010_make_palindrome_entail_wit_4_1.
Axiom proof_of_p010_make_palindrome_entail_wit_4_2 : p010_make_palindrome_entail_wit_4_2.
Axiom proof_of_p010_make_palindrome_entail_wit_5 : p010_make_palindrome_entail_wit_5.
Axiom proof_of_p010_make_palindrome_entail_wit_6 : p010_make_palindrome_entail_wit_6.
Axiom proof_of_p010_make_palindrome_entail_wit_7 : p010_make_palindrome_entail_wit_7.
Axiom proof_of_p010_make_palindrome_entail_wit_8 : p010_make_palindrome_entail_wit_8.
Axiom proof_of_p010_make_palindrome_entail_wit_9 : p010_make_palindrome_entail_wit_9.
Axiom proof_of_p010_make_palindrome_return_wit_1 : p010_make_palindrome_return_wit_1.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_1_pure : p010_make_palindrome_partial_solve_wit_1_pure.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_1 : p010_make_palindrome_partial_solve_wit_1.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_2_pure : p010_make_palindrome_partial_solve_wit_2_pure.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_2 : p010_make_palindrome_partial_solve_wit_2.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_3_pure : p010_make_palindrome_partial_solve_wit_3_pure.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_3 : p010_make_palindrome_partial_solve_wit_3.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_4 : p010_make_palindrome_partial_solve_wit_4.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_5 : p010_make_palindrome_partial_solve_wit_5.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_6 : p010_make_palindrome_partial_solve_wit_6.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_7 : p010_make_palindrome_partial_solve_wit_7.
Axiom proof_of_p010_make_palindrome_partial_solve_wit_8 : p010_make_palindrome_partial_solve_wit_8.

End VC_Correct.
