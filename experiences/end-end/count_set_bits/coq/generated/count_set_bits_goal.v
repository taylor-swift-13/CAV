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
Require Import count_set_bits.
Local Open Scope sac.

(*----- Function count_set_bits -----*)

Definition count_set_bits_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_set_bits_safety_wit_2 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition count_set_bits_safety_wit_3 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((n <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_set_bits_safety_wit_4 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_set_bits_safety_wit_5 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition count_set_bits_safety_wit_6 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition count_set_bits_safety_wit_7 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((n <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_set_bits_safety_wit_8 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_set_bits_safety_wit_9 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((n <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition count_set_bits_safety_wit_10 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition count_set_bits_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= n_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ ((0 + (count_set_bits_z (n_pre)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
.

Definition count_set_bits_entail_wit_2_1 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) = 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= (n ÷ 2 )) ” 
  &&  “ ((n ÷ 2 ) <= n_pre) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ (((count + 1 ) + (count_set_bits_z ((n ÷ 2 ))) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
.

Definition count_set_bits_entail_wit_2_2 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ ((n % ( 2 ) ) <> 1) ” 
  &&  “ (n > 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= (n ÷ 2 )) ” 
  &&  “ ((n ÷ 2 ) <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z ((n ÷ 2 ))) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
.

Definition count_set_bits_entail_wit_3 := 
forall (n_pre: Z) (count: Z) (n: Z) ,
  “ (n <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= n_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ”
  &&  emp
|--
  “ (n <= 0) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ”
  &&  emp
.

Definition count_set_bits_return_wit_1 := 
forall (n_pre: Z) (n: Z) (count: Z) ,
  “ (n <= 0) ” 
  &&  “ (0 <= count) ” 
  &&  “ ((count + (count_set_bits_z (n)) ) = (count_set_bits_z (n_pre))) ”
  &&  emp
|--
  “ (0 <= count) ” 
  &&  “ (count = (count_set_bits_z (n_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_count_set_bits_safety_wit_1 : count_set_bits_safety_wit_1.
Axiom proof_of_count_set_bits_safety_wit_2 : count_set_bits_safety_wit_2.
Axiom proof_of_count_set_bits_safety_wit_3 : count_set_bits_safety_wit_3.
Axiom proof_of_count_set_bits_safety_wit_4 : count_set_bits_safety_wit_4.
Axiom proof_of_count_set_bits_safety_wit_5 : count_set_bits_safety_wit_5.
Axiom proof_of_count_set_bits_safety_wit_6 : count_set_bits_safety_wit_6.
Axiom proof_of_count_set_bits_safety_wit_7 : count_set_bits_safety_wit_7.
Axiom proof_of_count_set_bits_safety_wit_8 : count_set_bits_safety_wit_8.
Axiom proof_of_count_set_bits_safety_wit_9 : count_set_bits_safety_wit_9.
Axiom proof_of_count_set_bits_safety_wit_10 : count_set_bits_safety_wit_10.
Axiom proof_of_count_set_bits_entail_wit_1 : count_set_bits_entail_wit_1.
Axiom proof_of_count_set_bits_entail_wit_2_1 : count_set_bits_entail_wit_2_1.
Axiom proof_of_count_set_bits_entail_wit_2_2 : count_set_bits_entail_wit_2_2.
Axiom proof_of_count_set_bits_entail_wit_3 : count_set_bits_entail_wit_3.
Axiom proof_of_count_set_bits_return_wit_1 : count_set_bits_return_wit_1.

End VC_Correct.
