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
Require Import armstrong_number.
Require Import armstrong_number_helper.
Local Open Scope sac.

(*----- Function armstrong_number -----*)

Definition armstrong_number_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "temp" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "temp" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "temp" ) )) # Int  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition armstrong_number_safety_wit_4 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_5 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_6 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ False ”
.

Definition armstrong_number_safety_wit_7 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ ((digits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits + 1 )) ”
.

Definition armstrong_number_safety_wit_8 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
|--
  “ ((temp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition armstrong_number_safety_wit_9 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition armstrong_number_safety_wit_10 := 
forall (n_pre: Z) (temp: Z) (digits: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> n_pre)
  **  ((( &( "digits" ) )) # Int  |-> digits)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_11 := 
forall (n_pre: Z) (digits: Z) (sum: Z) (sum_2: Z) (digits_2: Z) (temp: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((temp = 0) -> (sum_2 = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ ((temp > 0) -> ((sum_2 + (armstrong_sum_z (temp) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_12 := 
forall (n_pre: Z) (digits: Z) (sum: Z) (sum_2: Z) (digits_2: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((temp = 0) -> (sum_2 = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ ((temp > 0) -> ((sum_2 + (armstrong_sum_z (temp) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
|--
  “ ((temp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition armstrong_number_safety_wit_13 := 
forall (n_pre: Z) (digits: Z) (sum: Z) (sum_2: Z) (digits_2: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((temp = 0) -> (sum_2 = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ ((temp > 0) -> ((sum_2 + (armstrong_sum_z (temp) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition armstrong_number_safety_wit_14 := 
forall (n_pre: Z) (digits: Z) (sum: Z) (sum_2: Z) (digits_2: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((temp = 0) -> (sum_2 = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ ((temp > 0) -> ((sum_2 + (armstrong_sum_z (temp) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "d" ) )) # Int  |-> (temp % ( 10 ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition armstrong_number_safety_wit_15 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition armstrong_number_safety_wit_16 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d_2: Z) (p_2: Z) (p: Z) (i: Z) (d: Z) (sum_2: Z) (digits_2: Z) (temp_2: Z) ,
  “ (i < digits_2) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp_2) ” 
  &&  “ (temp_2 <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp_2) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp_2 % ( 10 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= digits_2) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (i))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d_2) ” 
  &&  “ (d_2 <= 9) ” 
  &&  “ (d_2 = (temp % ( 10 ) )) ” 
  &&  “ (p_2 = 1) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_2)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ ((p * d ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p * d )) ”
.

Definition armstrong_number_safety_wit_17 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) (p_2: Z) (i: Z) (d_2: Z) (sum_2: Z) (digits_2: Z) (temp_2: Z) ,
  “ (i < digits_2) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp_2) ” 
  &&  “ (temp_2 <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp_2) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d_2) ” 
  &&  “ (d_2 <= 9) ” 
  &&  “ (d_2 = (temp_2 % ( 10 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= digits_2) ” 
  &&  “ (0 <= p_2) ” 
  &&  “ (p_2 = (zpow_nat_z (d_2) (i))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp_2)
  **  ((( &( "digits" ) )) # Int  |-> digits_2)
  **  ((( &( "sum" ) )) # Int  |-> sum_2)
  **  ((( &( "d" ) )) # Int  |-> d_2)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "p" ) )) # Int  |-> (p_2 * d_2 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition armstrong_number_safety_wit_18 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (digits))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "sum" ) )) # Int  |-> sum)
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ ((sum + p ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + p )) ”
.

Definition armstrong_number_safety_wit_19 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (digits))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "sum" ) )) # Int  |-> (sum + p ))
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ ((temp <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition armstrong_number_safety_wit_20 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (digits))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "temp" ) )) # Int  |-> temp)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "sum" ) )) # Int  |-> (sum + p ))
  **  ((( &( "d" ) )) # Int  |-> d)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition armstrong_number_entail_wit_1_1 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((n_pre = 0) -> ((n_pre = 0) /\ (0 = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (n_pre)) + 0 ))) /\ ((n_pre = 0) -> (0 = (count_digits_z (n_pre))))) /\ ((n_pre > 0) -> ((0 + (count_digits_z (n_pre)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ ((n_pre = 0) -> ((n_pre = 0) /\ (0 = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (n_pre)) + 0 ))) /\ ((n_pre = 0) -> (0 = (count_digits_z (n_pre))))) /\ ((n_pre > 0) -> ((0 + (count_digits_z (n_pre)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
.

Definition armstrong_number_entail_wit_1_2 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ ((n_pre = 0) -> ((n_pre = 0) /\ (1 = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (n_pre)) + 1 ))) /\ ((n_pre = 0) -> (1 = (count_digits_z (n_pre))))) /\ ((n_pre > 0) -> ((1 + (count_digits_z (n_pre)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 <= 8) ” 
  &&  “ ((n_pre = 0) -> ((n_pre = 0) /\ (1 = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (n_pre)) + 1 ))) /\ ((n_pre = 0) -> (1 = (count_digits_z (n_pre))))) /\ ((n_pre > 0) -> ((1 + (count_digits_z (n_pre)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
.

Definition armstrong_number_entail_wit_2 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= (temp ÷ 10 )) ” 
  &&  “ ((temp ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ ((digits + 1 ) <= 8) ” 
  &&  “ ((n_pre = 0) -> (((temp ÷ 10 ) = 0) /\ ((digits + 1 ) = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z ((temp ÷ 10 ))) + (digits + 1 ) ))) /\ (((temp ÷ 10 ) = 0) -> ((digits + 1 ) = (count_digits_z (n_pre))))) /\ (((temp ÷ 10 ) > 0) -> (((digits + 1 ) + (count_digits_z ((temp ÷ 10 ))) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= (temp ÷ 10 )) ” 
  &&  “ ((temp ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ ((digits + 1 ) <= 8) ” 
  &&  “ ((n_pre = 0) -> (((temp ÷ 10 ) = 0) /\ ((digits + 1 ) = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z ((temp ÷ 10 ))) + (digits + 1 ) ))) /\ (((temp ÷ 10 ) = 0) -> ((digits + 1 ) = (count_digits_z (n_pre))))) /\ (((temp ÷ 10 ) > 0) -> (((digits + 1 ) + (count_digits_z ((temp ÷ 10 ))) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp)
.

Definition armstrong_number_entail_wit_3_1 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_3_2 := 
forall (n_pre: Z) (digits: Z) (temp: Z) ,
  “ (temp <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ ((n_pre = 0) -> ((temp = 0) /\ (digits = 1))) ” 
  &&  “ ((0 < n_pre) -> ((((0 < (count_digits_z (n_pre))) /\ (0 < ((count_digits_z (temp)) + digits ))) /\ ((temp = 0) -> (digits = (count_digits_z (n_pre))))) /\ ((temp > 0) -> ((digits + (count_digits_z (temp)) ) = (count_digits_z (n_pre)))))) ” 
  &&  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_4 := 
forall (n_pre: Z) (temp: Z) (digits: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((0 + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_5 := 
forall (n_pre: Z) (digits: Z) (sum: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((n_pre = 0) -> (sum = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ ((n_pre > 0) -> ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_6 := 
forall (n_pre: Z) (digits_2: Z) (sum_2: Z) (sum: Z) (digits: Z) (temp: Z) ,
  “ (temp > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((temp = 0) -> (sum = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ ((temp > 0) -> ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (sum_2 = 0) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (n_pre) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= (temp % ( 10 ) )) ” 
  &&  “ ((temp % ( 10 ) ) <= 9) ” 
  &&  “ ((temp % ( 10 ) ) = (temp % ( 10 ) )) ” 
  &&  “ (1 = 1) ”
  &&  emp
.

Definition armstrong_number_entail_wit_7 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  emp
.

Definition armstrong_number_entail_wit_8 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) (d: Z) (p: Z) (p_2: Z) (i: Z) (d_2: Z) (sum_2: Z) (digits_2: Z) (temp_2: Z) ,
  “ (i < digits_2) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp_2) ” 
  &&  “ (temp_2 <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp_2) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d_2) ” 
  &&  “ (d_2 <= 9) ” 
  &&  “ (d_2 = (temp_2 % ( 10 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= digits_2) ” 
  &&  “ (0 <= p_2) ” 
  &&  “ (p_2 = (zpow_nat_z (d_2) (i))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp_2) ” 
  &&  “ (temp_2 <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp_2) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d_2) ” 
  &&  “ (d_2 <= 9) ” 
  &&  “ (d_2 = (temp_2 % ( 10 ) )) ” 
  &&  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= digits_2) ” 
  &&  “ (0 <= (p_2 * d_2 )) ” 
  &&  “ ((p_2 * d_2 ) = (zpow_nat_z (d_2) ((i + 1 )))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (p = 1) ”
  &&  emp
.

Definition armstrong_number_entail_wit_9 := 
forall (n_pre: Z) (temp_2: Z) (digits_2: Z) (sum_2: Z) (d_2: Z) (p_2: Z) (p: Z) (i: Z) (d: Z) (sum: Z) (digits: Z) (temp: Z) ,
  “ (i >= digits) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= digits) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (i))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp_2) ” 
  &&  “ (temp_2 <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp_2) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d_2) ” 
  &&  “ (d_2 <= 9) ” 
  &&  “ (d_2 = (temp_2 % ( 10 ) )) ” 
  &&  “ (p_2 = 1) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (digits))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_10 := 
forall (n_pre: Z) (temp: Z) (digits_2: Z) (sum_2: Z) (d: Z) (p: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 < temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum_2) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (temp) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ” 
  &&  “ (0 <= d) ” 
  &&  “ (d <= 9) ” 
  &&  “ (d = (temp % ( 10 ) )) ” 
  &&  “ (0 <= p) ” 
  &&  “ (p = (zpow_nat_z (d) (digits_2))) ”
  &&  emp
|--
  EX (sum: Z)  (digits: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= (temp ÷ 10 )) ” 
  &&  “ ((temp ÷ 10 ) <= n_pre) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= (sum_2 + p )) ” 
  &&  “ (((temp ÷ 10 ) = 0) -> ((sum_2 + p ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (((temp ÷ 10 ) > 0) -> (((sum_2 + p ) + (armstrong_sum_z ((temp ÷ 10 )) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = 0) ” 
  &&  “ ((sum + (armstrong_sum_z (n_pre) (digits)) ) = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
.

Definition armstrong_number_entail_wit_11 := 
forall (n_pre: Z) (digits_2: Z) (sum_2: Z) (sum: Z) (digits: Z) (temp: Z) ,
  “ (temp <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (0 <= temp) ” 
  &&  “ (temp <= n_pre) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (0 <= sum) ” 
  &&  “ ((temp = 0) -> (sum = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ ((temp > 0) -> ((sum + (armstrong_sum_z (temp) (digits)) ) = (armstrong_sum_z (n_pre) (digits)))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 99999999) ” 
  &&  “ (1 <= digits_2) ” 
  &&  “ (digits_2 <= 8) ” 
  &&  “ (digits_2 = (count_digits_z (n_pre))) ” 
  &&  “ (sum_2 = 0) ” 
  &&  “ ((sum_2 + (armstrong_sum_z (n_pre) (digits_2)) ) = (armstrong_sum_z (n_pre) (digits_2))) ”
  &&  emp
|--
  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
.

Definition armstrong_number_return_wit_1 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) ,
  “ (sum = n_pre) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
|--
  “ (1 = (is_armstrong_z (n_pre))) ”
  &&  emp
.

Definition armstrong_number_return_wit_2 := 
forall (n_pre: Z) (temp: Z) (digits: Z) (sum: Z) ,
  “ (sum <> n_pre) ” 
  &&  “ (temp = 0) ” 
  &&  “ (1 <= digits) ” 
  &&  “ (digits <= 8) ” 
  &&  “ (digits = (count_digits_z (n_pre))) ” 
  &&  “ (sum = (armstrong_sum_z (n_pre) (digits))) ”
  &&  emp
|--
  “ (0 = (is_armstrong_z (n_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_armstrong_number_safety_wit_1 : armstrong_number_safety_wit_1.
Axiom proof_of_armstrong_number_safety_wit_2 : armstrong_number_safety_wit_2.
Axiom proof_of_armstrong_number_safety_wit_3 : armstrong_number_safety_wit_3.
Axiom proof_of_armstrong_number_safety_wit_4 : armstrong_number_safety_wit_4.
Axiom proof_of_armstrong_number_safety_wit_5 : armstrong_number_safety_wit_5.
Axiom proof_of_armstrong_number_safety_wit_6 : armstrong_number_safety_wit_6.
Axiom proof_of_armstrong_number_safety_wit_7 : armstrong_number_safety_wit_7.
Axiom proof_of_armstrong_number_safety_wit_8 : armstrong_number_safety_wit_8.
Axiom proof_of_armstrong_number_safety_wit_9 : armstrong_number_safety_wit_9.
Axiom proof_of_armstrong_number_safety_wit_10 : armstrong_number_safety_wit_10.
Axiom proof_of_armstrong_number_safety_wit_11 : armstrong_number_safety_wit_11.
Axiom proof_of_armstrong_number_safety_wit_12 : armstrong_number_safety_wit_12.
Axiom proof_of_armstrong_number_safety_wit_13 : armstrong_number_safety_wit_13.
Axiom proof_of_armstrong_number_safety_wit_14 : armstrong_number_safety_wit_14.
Axiom proof_of_armstrong_number_safety_wit_15 : armstrong_number_safety_wit_15.
Axiom proof_of_armstrong_number_safety_wit_16 : armstrong_number_safety_wit_16.
Axiom proof_of_armstrong_number_safety_wit_17 : armstrong_number_safety_wit_17.
Axiom proof_of_armstrong_number_safety_wit_18 : armstrong_number_safety_wit_18.
Axiom proof_of_armstrong_number_safety_wit_19 : armstrong_number_safety_wit_19.
Axiom proof_of_armstrong_number_safety_wit_20 : armstrong_number_safety_wit_20.
Axiom proof_of_armstrong_number_entail_wit_1_1 : armstrong_number_entail_wit_1_1.
Axiom proof_of_armstrong_number_entail_wit_1_2 : armstrong_number_entail_wit_1_2.
Axiom proof_of_armstrong_number_entail_wit_2 : armstrong_number_entail_wit_2.
Axiom proof_of_armstrong_number_entail_wit_3_1 : armstrong_number_entail_wit_3_1.
Axiom proof_of_armstrong_number_entail_wit_3_2 : armstrong_number_entail_wit_3_2.
Axiom proof_of_armstrong_number_entail_wit_4 : armstrong_number_entail_wit_4.
Axiom proof_of_armstrong_number_entail_wit_5 : armstrong_number_entail_wit_5.
Axiom proof_of_armstrong_number_entail_wit_6 : armstrong_number_entail_wit_6.
Axiom proof_of_armstrong_number_entail_wit_7 : armstrong_number_entail_wit_7.
Axiom proof_of_armstrong_number_entail_wit_8 : armstrong_number_entail_wit_8.
Axiom proof_of_armstrong_number_entail_wit_9 : armstrong_number_entail_wit_9.
Axiom proof_of_armstrong_number_entail_wit_10 : armstrong_number_entail_wit_10.
Axiom proof_of_armstrong_number_entail_wit_11 : armstrong_number_entail_wit_11.
Axiom proof_of_armstrong_number_return_wit_1 : armstrong_number_return_wit_1.
Axiom proof_of_armstrong_number_return_wit_2 : armstrong_number_return_wit_2.

End VC_Correct.
