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
Local Open Scope sac.

(*----- Function is_even -----*)

Definition is_even_safety_wit_1 := 
forall (n_pre: Z) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition is_even_safety_wit_2 := 
forall (n_pre: Z) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition is_even_safety_wit_3 := 
forall (n_pre: Z) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition is_even_return_wit_1 := 
forall (n_pre: Z) ,
  “ ((n_pre % ( 2 ) ) = 0) ”
  &&  emp
|--
  “ (((n_pre % ( 2 ) ) = 0) -> (1 = 1)) ” 
  &&  “ (((n_pre % ( 2 ) ) <> 0) -> (1 = 0)) ”
  &&  emp
.

Definition is_even_return_wit_2 := 
forall (n_pre: Z) ,
  “ ((n_pre % ( 2 ) ) <> 0) ”
  &&  emp
|--
  “ (((n_pre % ( 2 ) ) = 0) -> (0 = 1)) ” 
  &&  “ (((n_pre % ( 2 ) ) <> 0) -> (0 = 0)) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_is_even_safety_wit_1 : is_even_safety_wit_1.
Axiom proof_of_is_even_safety_wit_2 : is_even_safety_wit_2.
Axiom proof_of_is_even_safety_wit_3 : is_even_safety_wit_3.
Axiom proof_of_is_even_return_wit_1 : is_even_return_wit_1.
Axiom proof_of_is_even_return_wit_2 : is_even_return_wit_2.

End VC_Correct.
