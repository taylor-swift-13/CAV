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
Require Import p139_special_factorial.
Local Open Scope sac.

(*----- Function p139_special_factorial -----*)

Definition p139_special_factorial_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (problem_139_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ”
  &&  ((( &( "bfact" ) )) # Int64  |->_)
  **  ((( &( "fact" ) )) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p139_special_factorial_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (problem_139_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ”
  &&  ((( &( "fact" ) )) # Int64  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p139_special_factorial_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (problem_139_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "bfact" ) )) # Int64  |-> 1)
  **  ((( &( "fact" ) )) # Int64  |-> 1)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p139_special_factorial_safety_wit_4 := 
forall (n_pre: Z) (bfact: Z) (fact: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (fact = (factorial ((i - 1 )))) ” 
  &&  “ (bfact = (bfact_coq ((i - 1 )))) ” 
  &&  “ (1 <= fact) ” 
  &&  “ (fact <= 5040) ” 
  &&  “ (1 <= bfact) ” 
  &&  “ (bfact <= 125411328000) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> fact)
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((fact * i ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (fact * i )) ”
.

Definition p139_special_factorial_safety_wit_5 := 
forall (n_pre: Z) (bfact: Z) (fact: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (fact = (factorial ((i - 1 )))) ” 
  &&  “ (bfact = (bfact_coq ((i - 1 )))) ” 
  &&  “ (1 <= fact) ” 
  &&  “ (fact <= 5040) ” 
  &&  “ (1 <= bfact) ” 
  &&  “ (bfact <= 125411328000) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> bfact)
|--
  “ ((bfact * (fact * i ) ) <= 9223372036854775807) ” 
  &&  “ ((-9223372036854775808) <= (bfact * (fact * i ) )) ”
.

Definition p139_special_factorial_safety_wit_6 := 
forall (n_pre: Z) (bfact: Z) (fact: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (fact = (factorial ((i - 1 )))) ” 
  &&  “ (bfact = (bfact_coq ((i - 1 )))) ” 
  &&  “ (1 <= fact) ” 
  &&  “ (fact <= 5040) ” 
  &&  “ (1 <= bfact) ” 
  &&  “ (bfact <= 125411328000) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "fact" ) )) # Int64  |-> (fact * i ))
  **  ((( &( "bfact" ) )) # Int64  |-> (bfact * (fact * i ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p139_special_factorial_entail_wit_1 := 
forall (n_pre: Z) ,
  “ (problem_139_pre n_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ”
  &&  emp
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (1 = (factorial ((1 - 1 )))) ” 
  &&  “ (1 = (bfact_coq ((1 - 1 )))) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 5040) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= 125411328000) ”
  &&  emp
.

Definition p139_special_factorial_entail_wit_2 := 
forall (n_pre: Z) (bfact: Z) (fact: Z) (i: Z) ,
  “ (i <= n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (fact = (factorial ((i - 1 )))) ” 
  &&  “ (bfact = (bfact_coq ((i - 1 )))) ” 
  &&  “ (1 <= fact) ” 
  &&  “ (fact <= 5040) ” 
  &&  “ (1 <= bfact) ” 
  &&  “ (bfact <= 125411328000) ”
  &&  emp
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n_pre + 1 )) ” 
  &&  “ ((fact * i ) = (factorial (((i + 1 ) - 1 )))) ” 
  &&  “ ((bfact * (fact * i ) ) = (bfact_coq (((i + 1 ) - 1 )))) ” 
  &&  “ (1 <= (fact * i )) ” 
  &&  “ ((fact * i ) <= 5040) ” 
  &&  “ (1 <= (bfact * (fact * i ) )) ” 
  &&  “ ((bfact * (fact * i ) ) <= 125411328000) ”
  &&  emp
.

Definition p139_special_factorial_return_wit_1 := 
forall (n_pre: Z) (bfact: Z) (fact: Z) (i: Z) ,
  “ (i > n_pre) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 8) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n_pre + 1 )) ” 
  &&  “ (fact = (factorial ((i - 1 )))) ” 
  &&  “ (bfact = (bfact_coq ((i - 1 )))) ” 
  &&  “ (1 <= fact) ” 
  &&  “ (fact <= 5040) ” 
  &&  “ (1 <= bfact) ” 
  &&  “ (bfact <= 125411328000) ”
  &&  emp
|--
  “ (problem_139_spec n_pre bfact ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_p139_special_factorial_safety_wit_1 : p139_special_factorial_safety_wit_1.
Axiom proof_of_p139_special_factorial_safety_wit_2 : p139_special_factorial_safety_wit_2.
Axiom proof_of_p139_special_factorial_safety_wit_3 : p139_special_factorial_safety_wit_3.
Axiom proof_of_p139_special_factorial_safety_wit_4 : p139_special_factorial_safety_wit_4.
Axiom proof_of_p139_special_factorial_safety_wit_5 : p139_special_factorial_safety_wit_5.
Axiom proof_of_p139_special_factorial_safety_wit_6 : p139_special_factorial_safety_wit_6.
Axiom proof_of_p139_special_factorial_entail_wit_1 : p139_special_factorial_entail_wit_1.
Axiom proof_of_p139_special_factorial_entail_wit_2 : p139_special_factorial_entail_wit_2.
Axiom proof_of_p139_special_factorial_return_wit_1 : p139_special_factorial_return_wit_1.

End VC_Correct.
