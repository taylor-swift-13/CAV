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
Require Import ex_collatz_steps.
Local Open Scope sac.

(*----- Function ex_collatz_steps -----*)

Definition ex_collatz_steps_safety_wit_1 := 
forall (n_pre: Z) (fuel: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "steps" ) )) # Int  |->_)
  **  ((( &( "x" ) )) # Int64  |-> n_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_collatz_steps_safety_wit_2 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_collatz_steps_safety_wit_3 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ ((x <> (-9223372036854775808)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition ex_collatz_steps_safety_wit_4 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_collatz_steps_safety_wit_5 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_collatz_steps_safety_wit_6 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) = 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ ((x <> (-9223372036854775808)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition ex_collatz_steps_safety_wit_7 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) = 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition ex_collatz_steps_safety_wit_8 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (((3 * x ) + 1 ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= ((3 * x ) + 1 )) ”
.

Definition ex_collatz_steps_safety_wit_9 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ ((3 * x ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (3 * x )) ”
.

Definition ex_collatz_steps_safety_wit_10 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition ex_collatz_steps_safety_wit_11 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> x)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_collatz_steps_safety_wit_12 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> ((3 * x ) + 1 ))
|--
  “ ((steps + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (steps + 1 )) ”
.

Definition ex_collatz_steps_safety_wit_13 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) = 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "steps" ) )) # Int  |-> steps)
  **  ((( &( "x" ) )) # Int64  |-> (x ÷ 2 ))
|--
  “ ((steps + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (steps + 1 )) ”
.

Definition ex_collatz_steps_entail_wit_1 := 
forall (n_pre: Z) (fuel: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel n_pre (fuel - 0 ) ) ” 
  &&  “ ((0 + (ex_collatz_steps_fuel (n_pre) ((fuel - 0 ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
.

Definition ex_collatz_steps_entail_wit_2_1 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) = 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
|--
  “ (0 <= (steps + 1 )) ” 
  &&  “ ((steps + 1 ) <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel (x ÷ 2 ) (fuel - (steps + 1 ) ) ) ” 
  &&  “ (((steps + 1 ) + (ex_collatz_steps_fuel ((x ÷ 2 )) ((fuel - (steps + 1 ) ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
.

Definition ex_collatz_steps_entail_wit_2_2 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ ((x % ( 2 ) ) <> 0) ” 
  &&  “ (x <> 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
|--
  “ (0 <= (steps + 1 )) ” 
  &&  “ ((steps + 1 ) <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel ((3 * x ) + 1 ) (fuel - (steps + 1 ) ) ) ” 
  &&  “ (((steps + 1 ) + (ex_collatz_steps_fuel (((3 * x ) + 1 )) ((fuel - (steps + 1 ) ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
.

Definition ex_collatz_steps_return_wit_1 := 
forall (n_pre: Z) (fuel: Z) (x: Z) (steps: Z) ,
  “ (x = 1) ” 
  &&  “ (0 <= steps) ” 
  &&  “ (steps <= fuel) ” 
  &&  “ (ex_collatz_safe_fuel x (fuel - steps ) ) ” 
  &&  “ ((steps + (ex_collatz_steps_fuel (x) ((fuel - steps ))) ) = (ex_collatz_steps_fuel (n_pre) (fuel))) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (0 <= fuel) ” 
  &&  “ (fuel <= INT_MAX) ” 
  &&  “ (ex_collatz_safe_fuel n_pre fuel ) ”
  &&  emp
|--
  “ (steps = (ex_collatz_steps_fuel (n_pre) (fuel))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_collatz_steps_safety_wit_1 : ex_collatz_steps_safety_wit_1.
Axiom proof_of_ex_collatz_steps_safety_wit_2 : ex_collatz_steps_safety_wit_2.
Axiom proof_of_ex_collatz_steps_safety_wit_3 : ex_collatz_steps_safety_wit_3.
Axiom proof_of_ex_collatz_steps_safety_wit_4 : ex_collatz_steps_safety_wit_4.
Axiom proof_of_ex_collatz_steps_safety_wit_5 : ex_collatz_steps_safety_wit_5.
Axiom proof_of_ex_collatz_steps_safety_wit_6 : ex_collatz_steps_safety_wit_6.
Axiom proof_of_ex_collatz_steps_safety_wit_7 : ex_collatz_steps_safety_wit_7.
Axiom proof_of_ex_collatz_steps_safety_wit_8 : ex_collatz_steps_safety_wit_8.
Axiom proof_of_ex_collatz_steps_safety_wit_9 : ex_collatz_steps_safety_wit_9.
Axiom proof_of_ex_collatz_steps_safety_wit_10 : ex_collatz_steps_safety_wit_10.
Axiom proof_of_ex_collatz_steps_safety_wit_11 : ex_collatz_steps_safety_wit_11.
Axiom proof_of_ex_collatz_steps_safety_wit_12 : ex_collatz_steps_safety_wit_12.
Axiom proof_of_ex_collatz_steps_safety_wit_13 : ex_collatz_steps_safety_wit_13.
Axiom proof_of_ex_collatz_steps_entail_wit_1 : ex_collatz_steps_entail_wit_1.
Axiom proof_of_ex_collatz_steps_entail_wit_2_1 : ex_collatz_steps_entail_wit_2_1.
Axiom proof_of_ex_collatz_steps_entail_wit_2_2 : ex_collatz_steps_entail_wit_2_2.
Axiom proof_of_ex_collatz_steps_return_wit_1 : ex_collatz_steps_return_wit_1.

End VC_Correct.
