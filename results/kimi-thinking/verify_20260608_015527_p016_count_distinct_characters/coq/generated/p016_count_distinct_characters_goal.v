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
Require Import p016_count_distinct_characters string_bridge.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p016_count_distinct_characters -----*)

Definition p016_count_distinct_characters_safety_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_2 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "n" ) )) # Int  |-> retval)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_3 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "seen" ) )) # Int  |->_)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_4 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p016_count_distinct_characters_safety_wit_5 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p016_count_distinct_characters_safety_wit_6 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 )) ”
.

Definition p016_count_distinct_characters_safety_wit_7 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p016_count_distinct_characters_safety_wit_8 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_9 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_10 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "seen" ) )) # Int  |-> 0)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "c" ) )) # Int  |-> ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_11 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (65 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 65) ”
.

Definition p016_count_distinct_characters_safety_wit_12 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (90 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 90) ”
.

Definition p016_count_distinct_characters_safety_wit_13 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 )) ”
.

Definition p016_count_distinct_characters_safety_wit_14 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p016_count_distinct_characters_safety_wit_15 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> ((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p016_count_distinct_characters_safety_wit_16 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p016_count_distinct_characters_safety_wit_17 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "d" ) )) # Int  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p016_count_distinct_characters_safety_wit_18 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_19 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_20 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_21 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_22 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_23 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> 1)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_24 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p016_count_distinct_characters_safety_wit_25 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen = 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_26 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen = 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "seen" ) )) # Int  |-> seen)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "str" ) )) # Ptr  |-> str)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p016_count_distinct_characters_safety_wit_27 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen <> 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "str" ) )) # Ptr  |-> str)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p016_count_distinct_characters_safety_wit_28 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen = 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
  **  ((( &( "str" ) )) # Ptr  |-> str)
  **  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p016_count_distinct_characters_entail_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (retval: Z) ,
  “ (retval = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= retval) ” 
  &&  “ (retval < INT_MAX) ” 
  &&  “ (0 = (count_distinct_lower_upto (0) (l))) ”
  &&  (CharArray.full str_pre (retval + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_2_1 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state 0 i l ((Znth i (app (l) ((cons (0) (nil)))) 0) + 32 ) 0 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_2_2 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state 0 i l (Znth i (app (l) ((cons (0) (nil)))) 0) 0 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_2_3 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth i (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state 0 i l (Znth i (app (l) ((cons (0) (nil)))) 0) 0 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_1 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c 1 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_2 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c 1 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_3 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) = c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c 1 ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_4 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) > 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_5 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) < 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_3_6 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (((Znth j (app (l) ((cons (0) (nil)))) 0) + 32 ) <> c) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) <= 90) ” 
  &&  “ ((Znth j (app (l) ((cons (0) (nil)))) 0) >= 65) ” 
  &&  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state (j + 1 ) i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_4_1 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen = 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((count + 1 ) = (count_distinct_lower_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_entail_wit_4_2 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (seen <> 0) ” 
  &&  “ (j >= i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto ((i + 1 )) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_return_wit_1 := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ (i >= n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (problem_16_spec l count ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_partial_solve_wit_1_pure := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  ((( &( "n" ) )) # Int  |->_)
  **  ((( &( "str" ) )) # Ptr  |-> str_pre)
  **  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ”
.

Definition p016_count_distinct_characters_partial_solve_wit_1_aux := 
forall (str_pre: Z) (len: Z) (l: (@list Z)) ,
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (l) (0)) <> 0)) ” 
  &&  “ (0 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (l)) = len) ” 
  &&  “ (problem_16_pre l ) ” 
  &&  “ (ascii_range l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < len)) -> ((Znth (k_2) (l) (0)) <> 0)) ”
  &&  (CharArray.full str_pre (len + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_partial_solve_wit_1 := p016_count_distinct_characters_partial_solve_wit_1_pure -> p016_count_distinct_characters_partial_solve_wit_1_aux.

Definition p016_count_distinct_characters_partial_solve_wit_2 := 
forall (l: (@list Z)) (str: Z) (count: Z) (n: Z) (i: Z) ,
  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (i < n) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ”
  &&  (((str + (i * sizeof(CHAR) ) )) # Char  |-> (Znth i (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str i 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Definition p016_count_distinct_characters_partial_solve_wit_3 := 
forall (l: (@list Z)) (str: Z) (c: Z) (seen: Z) (count: Z) (n: Z) (i: Z) (j: Z) ,
  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (CharArray.full str (n + 1 ) (app (l) ((cons (0) (nil)))) )
|--
  “ (j < i) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= i) ” 
  &&  “ (i <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (count = (count_distinct_lower_upto (i) (l))) ” 
  &&  “ (lower_seen_state j i l c seen ) ”
  &&  (((str + (j * sizeof(CHAR) ) )) # Char  |-> (Znth j (app (l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i str j 0 (n + 1 ) (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p016_count_distinct_characters_safety_wit_1 : p016_count_distinct_characters_safety_wit_1.
Axiom proof_of_p016_count_distinct_characters_safety_wit_2 : p016_count_distinct_characters_safety_wit_2.
Axiom proof_of_p016_count_distinct_characters_safety_wit_3 : p016_count_distinct_characters_safety_wit_3.
Axiom proof_of_p016_count_distinct_characters_safety_wit_4 : p016_count_distinct_characters_safety_wit_4.
Axiom proof_of_p016_count_distinct_characters_safety_wit_5 : p016_count_distinct_characters_safety_wit_5.
Axiom proof_of_p016_count_distinct_characters_safety_wit_6 : p016_count_distinct_characters_safety_wit_6.
Axiom proof_of_p016_count_distinct_characters_safety_wit_7 : p016_count_distinct_characters_safety_wit_7.
Axiom proof_of_p016_count_distinct_characters_safety_wit_8 : p016_count_distinct_characters_safety_wit_8.
Axiom proof_of_p016_count_distinct_characters_safety_wit_9 : p016_count_distinct_characters_safety_wit_9.
Axiom proof_of_p016_count_distinct_characters_safety_wit_10 : p016_count_distinct_characters_safety_wit_10.
Axiom proof_of_p016_count_distinct_characters_safety_wit_11 : p016_count_distinct_characters_safety_wit_11.
Axiom proof_of_p016_count_distinct_characters_safety_wit_12 : p016_count_distinct_characters_safety_wit_12.
Axiom proof_of_p016_count_distinct_characters_safety_wit_13 : p016_count_distinct_characters_safety_wit_13.
Axiom proof_of_p016_count_distinct_characters_safety_wit_14 : p016_count_distinct_characters_safety_wit_14.
Axiom proof_of_p016_count_distinct_characters_safety_wit_15 : p016_count_distinct_characters_safety_wit_15.
Axiom proof_of_p016_count_distinct_characters_safety_wit_16 : p016_count_distinct_characters_safety_wit_16.
Axiom proof_of_p016_count_distinct_characters_safety_wit_17 : p016_count_distinct_characters_safety_wit_17.
Axiom proof_of_p016_count_distinct_characters_safety_wit_18 : p016_count_distinct_characters_safety_wit_18.
Axiom proof_of_p016_count_distinct_characters_safety_wit_19 : p016_count_distinct_characters_safety_wit_19.
Axiom proof_of_p016_count_distinct_characters_safety_wit_20 : p016_count_distinct_characters_safety_wit_20.
Axiom proof_of_p016_count_distinct_characters_safety_wit_21 : p016_count_distinct_characters_safety_wit_21.
Axiom proof_of_p016_count_distinct_characters_safety_wit_22 : p016_count_distinct_characters_safety_wit_22.
Axiom proof_of_p016_count_distinct_characters_safety_wit_23 : p016_count_distinct_characters_safety_wit_23.
Axiom proof_of_p016_count_distinct_characters_safety_wit_24 : p016_count_distinct_characters_safety_wit_24.
Axiom proof_of_p016_count_distinct_characters_safety_wit_25 : p016_count_distinct_characters_safety_wit_25.
Axiom proof_of_p016_count_distinct_characters_safety_wit_26 : p016_count_distinct_characters_safety_wit_26.
Axiom proof_of_p016_count_distinct_characters_safety_wit_27 : p016_count_distinct_characters_safety_wit_27.
Axiom proof_of_p016_count_distinct_characters_safety_wit_28 : p016_count_distinct_characters_safety_wit_28.
Axiom proof_of_p016_count_distinct_characters_entail_wit_1 : p016_count_distinct_characters_entail_wit_1.
Axiom proof_of_p016_count_distinct_characters_entail_wit_2_1 : p016_count_distinct_characters_entail_wit_2_1.
Axiom proof_of_p016_count_distinct_characters_entail_wit_2_2 : p016_count_distinct_characters_entail_wit_2_2.
Axiom proof_of_p016_count_distinct_characters_entail_wit_2_3 : p016_count_distinct_characters_entail_wit_2_3.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_1 : p016_count_distinct_characters_entail_wit_3_1.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_2 : p016_count_distinct_characters_entail_wit_3_2.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_3 : p016_count_distinct_characters_entail_wit_3_3.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_4 : p016_count_distinct_characters_entail_wit_3_4.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_5 : p016_count_distinct_characters_entail_wit_3_5.
Axiom proof_of_p016_count_distinct_characters_entail_wit_3_6 : p016_count_distinct_characters_entail_wit_3_6.
Axiom proof_of_p016_count_distinct_characters_entail_wit_4_1 : p016_count_distinct_characters_entail_wit_4_1.
Axiom proof_of_p016_count_distinct_characters_entail_wit_4_2 : p016_count_distinct_characters_entail_wit_4_2.
Axiom proof_of_p016_count_distinct_characters_return_wit_1 : p016_count_distinct_characters_return_wit_1.
Axiom proof_of_p016_count_distinct_characters_partial_solve_wit_1_pure : p016_count_distinct_characters_partial_solve_wit_1_pure.
Axiom proof_of_p016_count_distinct_characters_partial_solve_wit_1 : p016_count_distinct_characters_partial_solve_wit_1.
Axiom proof_of_p016_count_distinct_characters_partial_solve_wit_2 : p016_count_distinct_characters_partial_solve_wit_2.
Axiom proof_of_p016_count_distinct_characters_partial_solve_wit_3 : p016_count_distinct_characters_partial_solve_wit_3.

End VC_Correct.
