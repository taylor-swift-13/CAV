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
Require Import p055_fib.
Local Open Scope sac.

(*----- Function p055_fib -----*)

Definition p055_fib_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p055_fib_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p055_fib_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "c" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Int  |-> 1)
  **  ((( &( "a" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition p055_fib_safety_wit_4 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (a = (fib_seq ((i - 2 )))) ” 
  &&  “ (b = (fib_seq ((i - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> a)
  **  ((( &( "b" ) )) # Int  |-> b)
  **  ((( &( "c" ) )) # Int  |->_)
|--
  “ ((a + b ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (a + b )) ”
.

Definition p055_fib_safety_wit_5 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (a = (fib_seq ((i - 2 )))) ” 
  &&  “ (b = (fib_seq ((i - 1 )))) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "a" ) )) # Int  |-> b)
  **  ((( &( "b" ) )) # Int  |-> (a + b ))
  **  ((( &( "c" ) )) # Int  |-> (a + b ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p055_fib_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ”
  &&  emp
|--
  “ (2 <= 2) ” 
  &&  “ (2 <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (0 = (fib_seq ((2 - 2 )))) ” 
  &&  “ (1 = (fib_seq ((2 - 1 )))) ”
  &&  emp
.

Definition p055_fib_entail_wit_2 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (a = (fib_seq ((i - 2 )))) ” 
  &&  “ (b = (fib_seq ((i - 1 )))) ”
  &&  ((( &( "c" ) )) # Int  |-> (a + b ))
|--
  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (b = (fib_seq (((i + 1 ) - 2 )))) ” 
  &&  “ ((a + b ) = (fib_seq (((i + 1 ) - 1 )))) ”
  &&  ((( &( "c" ) )) # Int  |->_)
.

Definition p055_fib_return_wit_1 := 
forall (n_pre: Z) (b: Z) (a: Z) (i: Z) ,
  “ (i > n_pre) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre < 100) ” 
  &&  “ (problem_55_pre n_pre ) ” 
  &&  “ (fib_step_int_range n_pre ) ” 
  &&  “ (a = (fib_seq ((i - 2 )))) ” 
  &&  “ (b = (fib_seq ((i - 1 )))) ”
  &&  emp
|--
  “ (problem_55_spec n_pre b ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p055_fib_safety_wit_1 : p055_fib_safety_wit_1.
Axiom proof_of_p055_fib_safety_wit_2 : p055_fib_safety_wit_2.
Axiom proof_of_p055_fib_safety_wit_3 : p055_fib_safety_wit_3.
Axiom proof_of_p055_fib_safety_wit_4 : p055_fib_safety_wit_4.
Axiom proof_of_p055_fib_safety_wit_5 : p055_fib_safety_wit_5.
Axiom proof_of_p055_fib_entail_wit_1 : p055_fib_entail_wit_1.
Axiom proof_of_p055_fib_entail_wit_2 : p055_fib_entail_wit_2.
Axiom proof_of_p055_fib_return_wit_1 : p055_fib_return_wit_1.

End VC_Correct.
