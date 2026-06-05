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

(*----- Function xizi_avl_balance_factor -----*)

Definition xizi_avl_balance_factor_safety_wit_1 := 
forall (right_height_pre: Z) (left_height_pre: Z) ,
  “ (0 <= left_height_pre) ” 
  &&  “ (0 <= right_height_pre) ”
  &&  ((( &( "right_height" ) )) # Int  |-> right_height_pre)
  **  ((( &( "left_height" ) )) # Int  |-> left_height_pre)
|--
  “ ((left_height_pre - right_height_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (left_height_pre - right_height_pre )) ”
.

Definition xizi_avl_balance_factor_return_wit_1 := 
forall (right_height_pre: Z) (left_height_pre: Z) ,
  “ (0 <= left_height_pre) ” 
  &&  “ (0 <= right_height_pre) ”
  &&  emp
|--
  “ ((left_height_pre - right_height_pre ) = (left_height_pre - right_height_pre )) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_xizi_avl_balance_factor_safety_wit_1 : xizi_avl_balance_factor_safety_wit_1.
Axiom proof_of_xizi_avl_balance_factor_return_wit_1 : xizi_avl_balance_factor_return_wit_1.

End VC_Correct.
