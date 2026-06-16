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
Require Import p063_fibfib.
Local Open Scope sac.

(*----- Function p063_fibfib -----*)

Definition p063_fibfib_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p063_fibfib_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p063_fibfib_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p063_fibfib_safety_wit_4 := 
forall (n_pre: Z) ,
  “ (n_pre = 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p063_fibfib_safety_wit_5 := 
forall (n_pre: Z) ,
  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p063_fibfib_safety_wit_6 := 
forall (n_pre: Z) ,
  “ (n_pre = 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p063_fibfib_safety_wit_7 := 
forall (n_pre: Z) ,
  “ (n_pre <> 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p063_fibfib_safety_wit_8 := 
forall (n_pre: Z) ,
  “ (n_pre <> 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p063_fibfib_safety_wit_9 := 
forall (n_pre: Z) ,
  “ (n_pre <> 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p063_fibfib_safety_wit_10 := 
forall (n_pre: Z) ,
  “ (n_pre <> 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |-> 1)
  **  ((( &( "b" ) )) # Int  |-> 0)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (3 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 3) ”
.

Definition p063_fibfib_safety_wit_11 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (a = (fibfib ((i - 3 )))) ” 
  &&  “ (b = (fibfib ((i - 2 )))) ” 
  &&  “ (c = (fibfib ((i - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  “ (((a + b ) + c ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((a + b ) + c )) ”
.

Definition p063_fibfib_safety_wit_12 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (a = (fibfib ((i - 3 )))) ” 
  &&  “ (b = (fibfib ((i - 2 )))) ” 
  &&  “ (c = (fibfib ((i - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |-> c)
  **  ((( &( "next" ) )) # Int  |->_)
|--
  “ ((a + b ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + b )) ”
.

Definition p063_fibfib_safety_wit_13 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (a = (fibfib ((i - 3 )))) ” 
  &&  “ (b = (fibfib ((i - 2 )))) ” 
  &&  “ (c = (fibfib ((i - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> c)
  **  ((( &( "c" ) )) # Int  |-> ((a + b ) + c ))
  **  ((( &( "next" ) )) # Int  |-> ((a + b ) + c ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p063_fibfib_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (n_pre <> 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  emp
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= 3) ” 
  &&  “ (3 <= (n_pre + 1 )) ” 
  &&  “ (0 = (fibfib ((3 - 3 )))) ” 
  &&  “ (0 = (fibfib ((3 - 2 )))) ” 
  &&  “ (1 = (fibfib ((3 - 1 )))) ”
  &&  emp
.

Definition p063_fibfib_entail_wit_2 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (a = (fibfib ((i - 3 )))) ” 
  &&  “ (b = (fibfib ((i - 2 )))) ” 
  &&  “ (c = (fibfib ((i - 1 )))) ”
  &&  ((( &( "next" ) )) # Int  |-> ((a + b ) + c ))
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (b = (fibfib (((i + 1 ) - 3 )))) ” 
  &&  “ (c = (fibfib (((i + 1 ) - 2 )))) ” 
  &&  “ (((a + b ) + c ) = (fibfib (((i + 1 ) - 1 )))) ”
  &&  ((( &( "next" ) )) # Int  |->_)
.

Definition p063_fibfib_return_wit_1 := 
forall (n_pre: Z) (c: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i > n_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ” 
  &&  “ (3 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (a = (fibfib ((i - 3 )))) ” 
  &&  “ (b = (fibfib ((i - 2 )))) ” 
  &&  “ (c = (fibfib ((i - 1 )))) ”
  &&  emp
|--
  “ (problem_63_spec n_pre c ) ”
  &&  emp
.

Definition p063_fibfib_return_wit_2 := 
forall (n_pre: Z) ,
  “ (n_pre = 2) ” 
  &&  “ (n_pre <> 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  emp
|--
  “ (problem_63_spec n_pre 1 ) ”
  &&  emp
.

Definition p063_fibfib_return_wit_3 := 
forall (n_pre: Z) ,
  “ (n_pre = 1) ” 
  &&  “ (n_pre <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  emp
|--
  “ (problem_63_spec n_pre 0 ) ”
  &&  emp
.

Definition p063_fibfib_return_wit_4 := 
forall (n_pre: Z) ,
  “ (n_pre = 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_63_pre n_pre ) ” 
  &&  “ (fibfib_step_int_range n_pre ) ”
  &&  emp
|--
  “ (problem_63_spec n_pre 0 ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p063_fibfib_safety_wit_1 : p063_fibfib_safety_wit_1.
Axiom proof_of_p063_fibfib_safety_wit_2 : p063_fibfib_safety_wit_2.
Axiom proof_of_p063_fibfib_safety_wit_3 : p063_fibfib_safety_wit_3.
Axiom proof_of_p063_fibfib_safety_wit_4 : p063_fibfib_safety_wit_4.
Axiom proof_of_p063_fibfib_safety_wit_5 : p063_fibfib_safety_wit_5.
Axiom proof_of_p063_fibfib_safety_wit_6 : p063_fibfib_safety_wit_6.
Axiom proof_of_p063_fibfib_safety_wit_7 : p063_fibfib_safety_wit_7.
Axiom proof_of_p063_fibfib_safety_wit_8 : p063_fibfib_safety_wit_8.
Axiom proof_of_p063_fibfib_safety_wit_9 : p063_fibfib_safety_wit_9.
Axiom proof_of_p063_fibfib_safety_wit_10 : p063_fibfib_safety_wit_10.
Axiom proof_of_p063_fibfib_safety_wit_11 : p063_fibfib_safety_wit_11.
Axiom proof_of_p063_fibfib_safety_wit_12 : p063_fibfib_safety_wit_12.
Axiom proof_of_p063_fibfib_safety_wit_13 : p063_fibfib_safety_wit_13.
Axiom proof_of_p063_fibfib_entail_wit_1 : p063_fibfib_entail_wit_1.
Axiom proof_of_p063_fibfib_entail_wit_2 : p063_fibfib_entail_wit_2.
Axiom proof_of_p063_fibfib_return_wit_1 : p063_fibfib_return_wit_1.
Axiom proof_of_p063_fibfib_return_wit_2 : p063_fibfib_return_wit_2.
Axiom proof_of_p063_fibfib_return_wit_3 : p063_fibfib_return_wit_3.
Axiom proof_of_p063_fibfib_return_wit_4 : p063_fibfib_return_wit_4.

End VC_Correct.
