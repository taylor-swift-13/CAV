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

(*----- Function double_nonnegative -----*)

Definition double_nonnegative_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1073741823) ”
  &&  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + n_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + n_pre )) ”
.

Definition double_nonnegative_return_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= 1073741823) ”
  &&  emp
|--
  “ ((n_pre + n_pre ) = (n_pre + n_pre )) ” 
  &&  “ (0 <= (n_pre + n_pre )) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_double_nonnegative_safety_wit_1 : double_nonnegative_safety_wit_1.
Axiom proof_of_double_nonnegative_return_wit_1 : double_nonnegative_return_wit_1.

End VC_Correct.
