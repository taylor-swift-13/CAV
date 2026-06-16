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
Require Import p076_is_simple_power.
Local Open Scope sac.

(*----- Function p076_is_simple_power -----*)

Definition p076_is_simple_power_safety_wit_1 := 
forall (n_pre: Z) (x_pre: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p076_is_simple_power_safety_wit_2 := 
forall (n_pre: Z) (x_pre: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ”
  &&  ((( &( "p" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p076_is_simple_power_safety_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (100 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 100) ”
.

Definition p076_is_simple_power_safety_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p = x_pre) ” 
  &&  “ (count < 100) ” 
  &&  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p076_is_simple_power_safety_wit_5 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p < x_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < 100) ” 
  &&  “ (1 <= p) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((p * n_pre ) <= INT_MAX) ”
  &&  ((( &( "p" ) )) # Int  |-> p)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((p * n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p * n_pre )) ”
.

Definition p076_is_simple_power_safety_wit_6 := 
forall (n_pre: Z) (x_pre: Z) (c: Z) (p: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < 100) ” 
  &&  “ (sp_inv x_pre n_pre (c + 1 ) p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "count" ) )) # Int  |-> c)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ ((c + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c + 1 )) ”
.

Definition p076_is_simple_power_safety_wit_7 := 
forall (n_pre: Z) (x_pre: Z) (c: Z) (p: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < 100) ” 
  &&  “ (sp_inv x_pre n_pre (c + 1 ) p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "count" ) )) # Int  |-> c)
  **  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p076_is_simple_power_safety_wit_8 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (count >= 100) ” 
  &&  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p076_is_simple_power_safety_wit_9 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p > x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  ((( &( "x" ) )) # Int  |-> x_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
  **  ((( &( "p" ) )) # Int  |-> p)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p076_is_simple_power_entail_wit_1 := 
forall (n_pre: Z) (x_pre: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ”
  &&  emp
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 100) ” 
  &&  “ (sp_inv x_pre n_pre 0 1 ) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (x_pre * n_pre )) ”
  &&  emp
.

Definition p076_is_simple_power_entail_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p <> x_pre) ” 
  &&  “ (count < 100) ” 
  &&  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
|--
  “ (p < x_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < 100) ” 
  &&  “ (1 <= p) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((p * n_pre ) <= INT_MAX) ”
  &&  emp
.

Definition p076_is_simple_power_entail_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p < x_pre) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < 100) ” 
  &&  “ (1 <= p) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ ((p * n_pre ) <= INT_MAX) ”
  &&  emp
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count < 100) ” 
  &&  “ (sp_inv x_pre n_pre (count + 1 ) (p * n_pre ) ) ” 
  &&  “ (1 <= (p * n_pre )) ” 
  &&  “ ((p * n_pre ) <= (x_pre * n_pre )) ”
  &&  emp
.

Definition p076_is_simple_power_entail_wit_4 := 
forall (n_pre: Z) (x_pre: Z) (c: Z) (p: Z) ,
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= c) ” 
  &&  “ (c < 100) ” 
  &&  “ (sp_inv x_pre n_pre (c + 1 ) p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
|--
  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= (c + 1 )) ” 
  &&  “ ((c + 1 ) <= 100) ” 
  &&  “ (sp_inv x_pre n_pre (c + 1 ) p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
.

Definition p076_is_simple_power_return_wit_1 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p > x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
|--
  “ (is_simple_power_spec x_pre n_pre 0 ) ”
  &&  emp
.

Definition p076_is_simple_power_return_wit_2 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (count >= 100) ” 
  &&  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
|--
  “ (is_simple_power_spec x_pre n_pre 0 ) ”
  &&  emp
.

Definition p076_is_simple_power_return_wit_3 := 
forall (n_pre: Z) (x_pre: Z) (p: Z) (count: Z) ,
  “ (p = x_pre) ” 
  &&  “ (count < 100) ” 
  &&  “ (p <= x_pre) ” 
  &&  “ (1 <= x_pre) ” 
  &&  “ (x_pre <= INT_MAX) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= INT_MAX) ” 
  &&  “ ((x_pre * n_pre ) <= INT_MAX) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= 100) ” 
  &&  “ (sp_inv x_pre n_pre count p ) ” 
  &&  “ (1 <= p) ” 
  &&  “ (p <= (x_pre * n_pre )) ”
  &&  emp
|--
  “ (is_simple_power_spec x_pre n_pre 1 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p076_is_simple_power_safety_wit_1 : p076_is_simple_power_safety_wit_1.
Axiom proof_of_p076_is_simple_power_safety_wit_2 : p076_is_simple_power_safety_wit_2.
Axiom proof_of_p076_is_simple_power_safety_wit_3 : p076_is_simple_power_safety_wit_3.
Axiom proof_of_p076_is_simple_power_safety_wit_4 : p076_is_simple_power_safety_wit_4.
Axiom proof_of_p076_is_simple_power_safety_wit_5 : p076_is_simple_power_safety_wit_5.
Axiom proof_of_p076_is_simple_power_safety_wit_6 : p076_is_simple_power_safety_wit_6.
Axiom proof_of_p076_is_simple_power_safety_wit_7 : p076_is_simple_power_safety_wit_7.
Axiom proof_of_p076_is_simple_power_safety_wit_8 : p076_is_simple_power_safety_wit_8.
Axiom proof_of_p076_is_simple_power_safety_wit_9 : p076_is_simple_power_safety_wit_9.
Axiom proof_of_p076_is_simple_power_entail_wit_1 : p076_is_simple_power_entail_wit_1.
Axiom proof_of_p076_is_simple_power_entail_wit_2 : p076_is_simple_power_entail_wit_2.
Axiom proof_of_p076_is_simple_power_entail_wit_3 : p076_is_simple_power_entail_wit_3.
Axiom proof_of_p076_is_simple_power_entail_wit_4 : p076_is_simple_power_entail_wit_4.
Axiom proof_of_p076_is_simple_power_return_wit_1 : p076_is_simple_power_return_wit_1.
Axiom proof_of_p076_is_simple_power_return_wit_2 : p076_is_simple_power_return_wit_2.
Axiom proof_of_p076_is_simple_power_return_wit_3 : p076_is_simple_power_return_wit_3.

End VC_Correct.
