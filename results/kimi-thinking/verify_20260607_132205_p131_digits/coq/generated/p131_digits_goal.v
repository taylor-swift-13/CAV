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
Require Import p131_digits.
Local Open Scope sac.

(*----- Function p131_digits -----*)

Definition p131_digits_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |->_)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "prod" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_4 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> 0)
  **  ((( &( "prod" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ False ”
.

Definition p131_digits_safety_wit_5 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_6 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_7 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_8 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_9 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_10 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |->_)
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_11 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p131_digits_safety_wit_12 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (((n % ( 10 ) ) <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition p131_digits_safety_wit_13 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p131_digits_safety_wit_14 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p131_digits_safety_wit_15 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_16 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_17 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_18 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p131_digits_safety_wit_19 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition p131_digits_safety_wit_20 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((prod * (n % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prod * (n % ( 10 ) ) )) ”
.

Definition p131_digits_safety_wit_21 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_22 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_23 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_24 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_25 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_26 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_27 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ ((n <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p131_digits_safety_wit_28 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "d" ) )) # Int  |-> (n % ( 10 ) ))
  **  ((( &( "has" ) )) # Int  |-> 1)
  **  ((( &( "prod" ) )) # Int  |-> (prod * (n % ( 10 ) ) ))
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p131_digits_safety_wit_29 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_30 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_safety_wit_31 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ False ”
.

Definition p131_digits_safety_wit_32 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (has <> 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ False ”
.

Definition p131_digits_safety_wit_33 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  ((( &( "has" ) )) # Int  |-> has)
  **  ((( &( "prod" ) )) # Int  |-> prod)
  **  ((( &( "n" ) )) # Int  |-> n)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p131_digits_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (problem_131_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((tail_odd_prod (n_pre)) <= INT_MAX) ”
  &&  emp
|--
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) <= INT_MAX) ”
  &&  emp)
  ||
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (0 = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_1 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ (1 = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
  ||
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_2 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ (1 = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
  ||
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= (prod * (n % ( 10 ) ) )) ” 
  &&  “ (1 = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) ((prod * (n % ( 10 ) ) )) (1)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_3 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
  ||
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_entail_wit_2_4 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (((n % ( 10 ) ) % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
  ||
  (“ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has))) ” 
  &&  “ (0 <= (n ÷ 10 )) ” 
  &&  “ ((n ÷ 10 ) <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) ((n ÷ 10 )) (prod) (has)) <= INT_MAX) ”
  &&  emp)
.

Definition p131_digits_return_wit_1 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (has <> 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 1) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  “ (problem_131_spec n_pre prod ) ”
  &&  emp
.

Definition p131_digits_return_wit_2 := 
forall (n_pre: Z) (n: Z) (prod: Z) (has: Z) ,
  “ (has = 0) ” 
  &&  “ (n <= 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n_pre) (1) (0)) = (tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= prod) ” 
  &&  “ (has = 0) ” 
  &&  “ ((tail_odd_prod_fuel ((S ((S ((S ((S ((S ((S ((S ((S ((S ((S (O))))))))))))))))))))) (n) (prod) (has)) <= INT_MAX) ”
  &&  emp
|--
  “ (problem_131_spec n_pre 0 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p131_digits_safety_wit_1 : p131_digits_safety_wit_1.
Axiom proof_of_p131_digits_safety_wit_2 : p131_digits_safety_wit_2.
Axiom proof_of_p131_digits_safety_wit_3 : p131_digits_safety_wit_3.
Axiom proof_of_p131_digits_safety_wit_4 : p131_digits_safety_wit_4.
Axiom proof_of_p131_digits_safety_wit_5 : p131_digits_safety_wit_5.
Axiom proof_of_p131_digits_safety_wit_6 : p131_digits_safety_wit_6.
Axiom proof_of_p131_digits_safety_wit_7 : p131_digits_safety_wit_7.
Axiom proof_of_p131_digits_safety_wit_8 : p131_digits_safety_wit_8.
Axiom proof_of_p131_digits_safety_wit_9 : p131_digits_safety_wit_9.
Axiom proof_of_p131_digits_safety_wit_10 : p131_digits_safety_wit_10.
Axiom proof_of_p131_digits_safety_wit_11 : p131_digits_safety_wit_11.
Axiom proof_of_p131_digits_safety_wit_12 : p131_digits_safety_wit_12.
Axiom proof_of_p131_digits_safety_wit_13 : p131_digits_safety_wit_13.
Axiom proof_of_p131_digits_safety_wit_14 : p131_digits_safety_wit_14.
Axiom proof_of_p131_digits_safety_wit_15 : p131_digits_safety_wit_15.
Axiom proof_of_p131_digits_safety_wit_16 : p131_digits_safety_wit_16.
Axiom proof_of_p131_digits_safety_wit_17 : p131_digits_safety_wit_17.
Axiom proof_of_p131_digits_safety_wit_18 : p131_digits_safety_wit_18.
Axiom proof_of_p131_digits_safety_wit_19 : p131_digits_safety_wit_19.
Axiom proof_of_p131_digits_safety_wit_20 : p131_digits_safety_wit_20.
Axiom proof_of_p131_digits_safety_wit_21 : p131_digits_safety_wit_21.
Axiom proof_of_p131_digits_safety_wit_22 : p131_digits_safety_wit_22.
Axiom proof_of_p131_digits_safety_wit_23 : p131_digits_safety_wit_23.
Axiom proof_of_p131_digits_safety_wit_24 : p131_digits_safety_wit_24.
Axiom proof_of_p131_digits_safety_wit_25 : p131_digits_safety_wit_25.
Axiom proof_of_p131_digits_safety_wit_26 : p131_digits_safety_wit_26.
Axiom proof_of_p131_digits_safety_wit_27 : p131_digits_safety_wit_27.
Axiom proof_of_p131_digits_safety_wit_28 : p131_digits_safety_wit_28.
Axiom proof_of_p131_digits_safety_wit_29 : p131_digits_safety_wit_29.
Axiom proof_of_p131_digits_safety_wit_30 : p131_digits_safety_wit_30.
Axiom proof_of_p131_digits_safety_wit_31 : p131_digits_safety_wit_31.
Axiom proof_of_p131_digits_safety_wit_32 : p131_digits_safety_wit_32.
Axiom proof_of_p131_digits_safety_wit_33 : p131_digits_safety_wit_33.
Axiom proof_of_p131_digits_entail_wit_1 : p131_digits_entail_wit_1.
Axiom proof_of_p131_digits_entail_wit_2_1 : p131_digits_entail_wit_2_1.
Axiom proof_of_p131_digits_entail_wit_2_2 : p131_digits_entail_wit_2_2.
Axiom proof_of_p131_digits_entail_wit_2_3 : p131_digits_entail_wit_2_3.
Axiom proof_of_p131_digits_entail_wit_2_4 : p131_digits_entail_wit_2_4.
Axiom proof_of_p131_digits_return_wit_1 : p131_digits_return_wit_1.
Axiom proof_of_p131_digits_return_wit_2 : p131_digits_return_wit_2.

End VC_Correct.
