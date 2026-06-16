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
Require Import p048_is_palindrome.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p048_is_palindrome -----*)

Definition p048_is_palindrome_safety_wit_1 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p048_is_palindrome_safety_wit_2 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p048_is_palindrome_safety_wit_3 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p048_is_palindrome_safety_wit_4 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition p048_is_palindrome_safety_wit_5 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p048_is_palindrome_safety_wit_6 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (j: Z) ,
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ” 
  &&  “ ((Znth (i) (l) (0)) <> (Znth (j) (l) (0))) ”
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p048_is_palindrome_safety_wit_7 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p048_is_palindrome_safety_wit_8 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p048_is_palindrome_safety_wit_9 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ ((j - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j - 1 )) ”
.

Definition p048_is_palindrome_safety_wit_10 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> (i + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p048_is_palindrome_safety_wit_11 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (j: Z) ,
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (j <= i) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p048_is_palindrome_entail_wit_1 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((Znth (k_4) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= (retval - 1 )) ” 
  &&  “ (0 <= ((retval - 1 ) + 1 )) ” 
  &&  “ ((retval - 1 ) < n) ” 
  &&  “ ((0 + (retval - 1 ) ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < 0)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_entail_wit_2 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <> (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (l) (0)) = (Znth (((n - 1 ) - k_4 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ” 
  &&  “ ((Znth (i) (l) (0)) <> (Znth (j) (l) (0))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_entail_wit_3 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) = (Znth j (app (l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ (0 <= (j - 1 )) ” 
  &&  “ ((i + 1 ) <= ((j - 1 ) + 1 )) ” 
  &&  “ ((j - 1 ) < n) ” 
  &&  “ (((i + 1 ) + (j - 1 ) ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < (i + 1 ))) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_entail_wit_4 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i >= j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < i)) -> ((Znth (k_4) (l) (0)) = (Znth (((n - 1 ) - k_4 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (j <= i) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_return_wit_1 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (j: Z) ,
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < n) ” 
  &&  “ (j <= i) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (k_3) (l) (0)) = (Znth (((n - 1 ) - k_3 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_48_spec l 1 ) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_return_wit_2 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (i: Z) (j: Z) ,
  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i < j) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < i)) -> ((Znth (k_3) (l) (0)) = (Znth (((n - 1 ) - k_3 )) (l) (0)))) ” 
  &&  “ ((Znth (i) (l) (0)) <> (Znth (j) (l) (0))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_48_spec l 0 ) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_return_wit_3 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = 0) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (problem_48_spec l 1 ) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_partial_solve_wit_1_pure := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "text" ) )) # Ptr  |-> text_pre)
  **  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p048_is_palindrome_partial_solve_wit_1_aux := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_partial_solve_wit_1 := p048_is_palindrome_partial_solve_wit_1_pure -> p048_is_palindrome_partial_solve_wit_1_aux.

Definition p048_is_palindrome_partial_solve_wit_2 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (((text_pre + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p048_is_palindrome_partial_solve_wit_3 := 
forall (text_pre: Z) (n: Z) (l: (@list Z)) (j: Z) (i: Z) ,
  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (CharArray.full text_pre (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < j) ” 
  &&  “ (0 < n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (problem_48_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ (0 <= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (i <= (j + 1 )) ” 
  &&  “ (j < n) ” 
  &&  “ ((i + j ) = (n - 1 )) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < i)) -> ((Znth (k_2) (l) (0)) = (Znth (((n - 1 ) - k_2 )) (l) (0)))) ”
  &&  (((text_pre + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i text_pre j 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p048_is_palindrome_safety_wit_1 : p048_is_palindrome_safety_wit_1.
Axiom proof_of_p048_is_palindrome_safety_wit_2 : p048_is_palindrome_safety_wit_2.
Axiom proof_of_p048_is_palindrome_safety_wit_3 : p048_is_palindrome_safety_wit_3.
Axiom proof_of_p048_is_palindrome_safety_wit_4 : p048_is_palindrome_safety_wit_4.
Axiom proof_of_p048_is_palindrome_safety_wit_5 : p048_is_palindrome_safety_wit_5.
Axiom proof_of_p048_is_palindrome_safety_wit_6 : p048_is_palindrome_safety_wit_6.
Axiom proof_of_p048_is_palindrome_safety_wit_7 : p048_is_palindrome_safety_wit_7.
Axiom proof_of_p048_is_palindrome_safety_wit_8 : p048_is_palindrome_safety_wit_8.
Axiom proof_of_p048_is_palindrome_safety_wit_9 : p048_is_palindrome_safety_wit_9.
Axiom proof_of_p048_is_palindrome_safety_wit_10 : p048_is_palindrome_safety_wit_10.
Axiom proof_of_p048_is_palindrome_safety_wit_11 : p048_is_palindrome_safety_wit_11.
Axiom proof_of_p048_is_palindrome_entail_wit_1 : p048_is_palindrome_entail_wit_1.
Axiom proof_of_p048_is_palindrome_entail_wit_2 : p048_is_palindrome_entail_wit_2.
Axiom proof_of_p048_is_palindrome_entail_wit_3 : p048_is_palindrome_entail_wit_3.
Axiom proof_of_p048_is_palindrome_entail_wit_4 : p048_is_palindrome_entail_wit_4.
Axiom proof_of_p048_is_palindrome_return_wit_1 : p048_is_palindrome_return_wit_1.
Axiom proof_of_p048_is_palindrome_return_wit_2 : p048_is_palindrome_return_wit_2.
Axiom proof_of_p048_is_palindrome_return_wit_3 : p048_is_palindrome_return_wit_3.
Axiom proof_of_p048_is_palindrome_partial_solve_wit_1_pure : p048_is_palindrome_partial_solve_wit_1_pure.
Axiom proof_of_p048_is_palindrome_partial_solve_wit_1 : p048_is_palindrome_partial_solve_wit_1.
Axiom proof_of_p048_is_palindrome_partial_solve_wit_2 : p048_is_palindrome_partial_solve_wit_2.
Axiom proof_of_p048_is_palindrome_partial_solve_wit_3 : p048_is_palindrome_partial_solve_wit_3.

End VC_Correct.
