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
Require Import p044_change_base.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p044_change_base -----*)

Definition p044_change_base_safety_wit_1 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_2 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "out0" ) )) # Ptr  |->_)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p044_change_base_safety_wit_3 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out0" ) )) # Ptr  |-> retval)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_4 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_full retval 2 )
  **  ((( &( "out0" ) )) # Ptr  |-> retval)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p044_change_base_safety_wit_5 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out0" ) )) # Ptr  |-> retval)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p044_change_base_safety_wit_6 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "out0" ) )) # Ptr  |-> retval)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_7 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_8 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "total" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> x_pre)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_9 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> x_pre)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_10 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "out" ) )) # Ptr  |-> 0)
  **  ((( &( "total" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> x_pre)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_11 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_12 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t > 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((digits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits + 1 )) ”
.

Definition p044_change_base_safety_wit_13 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t > 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p044_change_base_safety_wit_14 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t > 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((t <> (INT_MIN)) \/ (base_pre <> (-1))) ” 
  &&  “ (base_pre <> 0) ”
.

Definition p044_change_base_safety_wit_15 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((digits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits + 1 )) ”
.

Definition p044_change_base_safety_wit_16 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p044_change_base_safety_wit_17 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.undef_full retval (digits + 1 ) )
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_18 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (digits: Z) (total: Z) (i: Z) ,
  “ (i <= total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_19 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (digits: Z) (total: Z) (i: Z) ,
  “ (i <= total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p044_change_base_safety_wit_20 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_21 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (x <= 0) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p044_change_base_safety_wit_22 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (x <= 0) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ False ”
.

Definition p044_change_base_safety_wit_23 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ ((digits - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits - 1 )) ”
.

Definition p044_change_base_safety_wit_24 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p044_change_base_safety_wit_25 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> (digits - 1 ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ ((48 + (x % ( base_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (x % ( base_pre ) ) )) ”
.

Definition p044_change_base_safety_wit_26 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> (digits - 1 ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ ((x <> (INT_MIN)) \/ (base_pre <> (-1))) ” 
  &&  “ (base_pre <> 0) ”
.

Definition p044_change_base_safety_wit_27 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> (digits - 1 ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p044_change_base_safety_wit_28 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (0 <= (total + 1 )) ” 
  &&  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (replace_Znth ((digits - 1 )) ((signed_last_nbits ((48 + (x % ( base_pre ) ) )) (8))) ((app (out_l) ((cons (0) (nil)))))) )
  **  ((( &( "digits" ) )) # Int  |-> (digits - 1 ))
  **  ((( &( "x" ) )) # Int  |-> x)
  **  ((( &( "total" ) )) # Int  |-> total)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((x <> (INT_MIN)) \/ (base_pre <> (-1))) ” 
  &&  “ (base_pre <> 0) ”
.

Definition p044_change_base_entail_wit_1 := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre <> 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  emp
|--
  “ (base_count_state x_pre base_pre x_pre 0 ) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 < INT_MAX) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  emp
.

Definition p044_change_base_entail_wit_2 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t > 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  emp
|--
  “ (base_count_state x_pre base_pre (t ÷ base_pre ) (digits + 1 ) ) ” 
  &&  “ (0 <= (t ÷ base_pre )) ” 
  &&  “ ((t ÷ base_pre ) < INT_MAX) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ ((digits + 1 ) < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  emp
.

Definition p044_change_base_entail_wit_3 := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.undef_full retval (digits + 1 ) )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ (digits = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = digits) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full retval 0 (repeat_Z (0) (0)) )
  **  (CharArray.undef_seg retval 0 (digits + 1 ) )
.

Definition p044_change_base_entail_wit_4 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (digits: Z) (total: Z) (i: Z) ,
  “ (i <= total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (i + 1 ) (app ((repeat_Z (0) (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (i + 1 ) (repeat_Z (0) ((i + 1 ))) )
  **  (CharArray.undef_seg out (i + 1 ) (total + 1 ) )
.

Definition p044_change_base_entail_wit_5 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (digits: Z) (total: Z) (i: Z) ,
  “ (i > total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  (EX (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre x_pre digits out_l ) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre x_pre digits out_l ) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (x_pre <= 0) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) ))
.

Definition p044_change_base_entail_wit_6 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l_2: (@list Z)) ,
  “ (0 <= (total + 1 )) ” 
  &&  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l_2 ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (replace_Znth ((digits - 1 )) ((signed_last_nbits ((48 + (x % ( base_pre ) ) )) (8))) ((app (out_l_2) ((cons (0) (nil)))))) )
|--
  (EX (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre (x ÷ base_pre ) (digits - 1 ) out_l ) ” 
  &&  “ (0 <= (x ÷ base_pre )) ” 
  &&  “ ((x ÷ base_pre ) < INT_MAX) ” 
  &&  “ (0 <= (digits - 1 )) ” 
  &&  “ ((digits - 1 ) <= total) ” 
  &&  “ (1 <= (digits - 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) ))
  ||
  (EX (out_l: (@list Z)) ,
  “ (base_fill_full_state x_pre base_pre (x ÷ base_pre ) (digits - 1 ) out_l ) ” 
  &&  “ (0 <= (x ÷ base_pre )) ” 
  &&  “ ((x ÷ base_pre ) < INT_MAX) ” 
  &&  “ (0 <= (digits - 1 )) ” 
  &&  “ ((digits - 1 ) <= total) ” 
  &&  “ ((x ÷ base_pre ) <= 0) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) ))
.

Definition p044_change_base_return_wit_1 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l_2: (@list Z)) ,
  “ (x <= 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l_2 ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (out_l) (0)) <> 0)) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (out_l)) = len) ” 
  &&  “ (problem_44_spec x_pre base_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p044_change_base_return_wit_2 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l_2: (@list Z)) ,
  “ (x <= 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l_2 ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (x <= 0) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l_2) ((cons (0) (nil)))) )
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (out_l) (0)) <> 0)) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (out_l)) = len) ” 
  &&  “ (problem_44_spec x_pre base_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p044_change_base_return_wit_3 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_seg retval (1 + 1 ) 2 )
  **  (((retval + (1 * sizeof(CHAR) ) )) # Char  |-> 0)
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  EX (out_l: (@list Z))  (len: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (out_l) (0)) <> 0)) ” 
  &&  “ (1 <= len) ” 
  &&  “ (len < INT_MAX) ” 
  &&  “ ((Zlength (out_l)) = len) ” 
  &&  “ (problem_44_spec x_pre base_pre out_l ) ”
  &&  (CharArray.full retval (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Definition p044_change_base_partial_solve_wit_1_pure := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  ((( &( "out0" ) )) # Ptr  |->_)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (2 > 0) ”
.

Definition p044_change_base_partial_solve_wit_1_aux := 
forall (base_pre: Z) (x_pre: Z) ,
  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  emp
|--
  “ (2 > 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  emp
.

Definition p044_change_base_partial_solve_wit_1 := p044_change_base_partial_solve_wit_1_pure -> p044_change_base_partial_solve_wit_1_aux.

Definition p044_change_base_partial_solve_wit_2 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_full retval 2 )
|--
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 2 )
.

Definition p044_change_base_partial_solve_wit_3 := 
forall (base_pre: Z) (x_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (CharArray.undef_seg retval (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (retval <> 0) ” 
  &&  “ (x_pre = 0) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ” 
  &&  “ (problem_44_pre x_pre base_pre ) ”
  &&  (((retval + (1 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 1 (0 + 1 ) 2 )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
.

Definition p044_change_base_partial_solve_wit_4_pure := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "total" ) )) # Int  |-> digits)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ ((digits + 1 ) > 0) ”
.

Definition p044_change_base_partial_solve_wit_4_aux := 
forall (base_pre: Z) (x_pre: Z) (i: Z) (out: Z) (total: Z) (t: Z) (digits: Z) ,
  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  emp
|--
  “ ((digits + 1 ) > 0) ” 
  &&  “ (t <= 0) ” 
  &&  “ (base_count_state x_pre base_pre t digits ) ” 
  &&  “ (0 <= t) ” 
  &&  “ (t < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits < INT_MAX) ” 
  &&  “ (total = 0) ” 
  &&  “ (out = 0) ” 
  &&  “ (i = 0) ” 
  &&  “ (0 < x_pre) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  emp
.

Definition p044_change_base_partial_solve_wit_4 := p044_change_base_partial_solve_wit_4_pure -> p044_change_base_partial_solve_wit_4_aux.

Definition p044_change_base_partial_solve_wit_5 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (digits: Z) (total: Z) (i: Z) ,
  “ (i <= total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out i (repeat_Z (0) (i)) )
  **  (CharArray.undef_seg out i (total + 1 ) )
|--
  “ (i <= total) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= (total + 1 )) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (digits = total) ” 
  &&  “ (t = 0) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (0 <= x_pre) ” 
  &&  “ (x_pre < INT_MAX) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (((out + (i * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out i i (total + 1 ) )
  **  (CharArray.full out i (repeat_Z (0) (i)) )
.

Definition p044_change_base_partial_solve_wit_6 := 
forall (base_pre: Z) (x_pre: Z) (out: Z) (t: Z) (i: Z) (total: Z) (x: Z) (digits: Z) (out_l: (@list Z)) ,
  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (CharArray.full out (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
|--
  “ (0 <= (total + 1 )) ” 
  &&  “ (x > 0) ” 
  &&  “ (base_fill_full_state x_pre base_pre x digits out_l ) ” 
  &&  “ (0 <= x) ” 
  &&  “ (x < INT_MAX) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= total) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (total = (Zlength ((base_digits_pos (x_pre) (base_pre))))) ” 
  &&  “ (1 <= total) ” 
  &&  “ (total < INT_MAX) ” 
  &&  “ (i = (total + 1 )) ” 
  &&  “ (t = 0) ” 
  &&  “ (2 <= base_pre) ” 
  &&  “ (base_pre < 10) ”
  &&  (((out + ((digits - 1 ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out (digits - 1 ) 0 (total + 1 ) (app (out_l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p044_change_base_safety_wit_1 : p044_change_base_safety_wit_1.
Axiom proof_of_p044_change_base_safety_wit_2 : p044_change_base_safety_wit_2.
Axiom proof_of_p044_change_base_safety_wit_3 : p044_change_base_safety_wit_3.
Axiom proof_of_p044_change_base_safety_wit_4 : p044_change_base_safety_wit_4.
Axiom proof_of_p044_change_base_safety_wit_5 : p044_change_base_safety_wit_5.
Axiom proof_of_p044_change_base_safety_wit_6 : p044_change_base_safety_wit_6.
Axiom proof_of_p044_change_base_safety_wit_7 : p044_change_base_safety_wit_7.
Axiom proof_of_p044_change_base_safety_wit_8 : p044_change_base_safety_wit_8.
Axiom proof_of_p044_change_base_safety_wit_9 : p044_change_base_safety_wit_9.
Axiom proof_of_p044_change_base_safety_wit_10 : p044_change_base_safety_wit_10.
Axiom proof_of_p044_change_base_safety_wit_11 : p044_change_base_safety_wit_11.
Axiom proof_of_p044_change_base_safety_wit_12 : p044_change_base_safety_wit_12.
Axiom proof_of_p044_change_base_safety_wit_13 : p044_change_base_safety_wit_13.
Axiom proof_of_p044_change_base_safety_wit_14 : p044_change_base_safety_wit_14.
Axiom proof_of_p044_change_base_safety_wit_15 : p044_change_base_safety_wit_15.
Axiom proof_of_p044_change_base_safety_wit_16 : p044_change_base_safety_wit_16.
Axiom proof_of_p044_change_base_safety_wit_17 : p044_change_base_safety_wit_17.
Axiom proof_of_p044_change_base_safety_wit_18 : p044_change_base_safety_wit_18.
Axiom proof_of_p044_change_base_safety_wit_19 : p044_change_base_safety_wit_19.
Axiom proof_of_p044_change_base_safety_wit_20 : p044_change_base_safety_wit_20.
Axiom proof_of_p044_change_base_safety_wit_21 : p044_change_base_safety_wit_21.
Axiom proof_of_p044_change_base_safety_wit_22 : p044_change_base_safety_wit_22.
Axiom proof_of_p044_change_base_safety_wit_23 : p044_change_base_safety_wit_23.
Axiom proof_of_p044_change_base_safety_wit_24 : p044_change_base_safety_wit_24.
Axiom proof_of_p044_change_base_safety_wit_25 : p044_change_base_safety_wit_25.
Axiom proof_of_p044_change_base_safety_wit_26 : p044_change_base_safety_wit_26.
Axiom proof_of_p044_change_base_safety_wit_27 : p044_change_base_safety_wit_27.
Axiom proof_of_p044_change_base_safety_wit_28 : p044_change_base_safety_wit_28.
Axiom proof_of_p044_change_base_entail_wit_1 : p044_change_base_entail_wit_1.
Axiom proof_of_p044_change_base_entail_wit_2 : p044_change_base_entail_wit_2.
Axiom proof_of_p044_change_base_entail_wit_3 : p044_change_base_entail_wit_3.
Axiom proof_of_p044_change_base_entail_wit_4 : p044_change_base_entail_wit_4.
Axiom proof_of_p044_change_base_entail_wit_5 : p044_change_base_entail_wit_5.
Axiom proof_of_p044_change_base_entail_wit_6 : p044_change_base_entail_wit_6.
Axiom proof_of_p044_change_base_return_wit_1 : p044_change_base_return_wit_1.
Axiom proof_of_p044_change_base_return_wit_2 : p044_change_base_return_wit_2.
Axiom proof_of_p044_change_base_return_wit_3 : p044_change_base_return_wit_3.
Axiom proof_of_p044_change_base_partial_solve_wit_1_pure : p044_change_base_partial_solve_wit_1_pure.
Axiom proof_of_p044_change_base_partial_solve_wit_1 : p044_change_base_partial_solve_wit_1.
Axiom proof_of_p044_change_base_partial_solve_wit_2 : p044_change_base_partial_solve_wit_2.
Axiom proof_of_p044_change_base_partial_solve_wit_3 : p044_change_base_partial_solve_wit_3.
Axiom proof_of_p044_change_base_partial_solve_wit_4_pure : p044_change_base_partial_solve_wit_4_pure.
Axiom proof_of_p044_change_base_partial_solve_wit_4 : p044_change_base_partial_solve_wit_4.
Axiom proof_of_p044_change_base_partial_solve_wit_5 : p044_change_base_partial_solve_wit_5.
Axiom proof_of_p044_change_base_partial_solve_wit_6 : p044_change_base_partial_solve_wit_6.

End VC_Correct.
