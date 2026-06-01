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

(*----- Function xizi_stack_range_check -----*)

Definition xizi_stack_range_check_safety_wit_1 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre > stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  ((( &( "stack_depth" ) )) # Int  |-> stack_depth_pre)
  **  ((( &( "stack_start" ) )) # Int  |-> stack_start_pre)
  **  ((( &( "sp" ) )) # Int  |-> sp_pre)
|--
  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
.

Definition xizi_stack_range_check_safety_wit_2 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre > (stack_start_pre + stack_depth_pre )) ”
  &&  “ (sp_pre > stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  ((( &( "stack_depth" ) )) # Int  |-> stack_depth_pre)
  **  ((( &( "stack_start" ) )) # Int  |-> stack_start_pre)
  **  ((( &( "sp" ) )) # Int  |-> sp_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_stack_range_check_safety_wit_3 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre <= stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  ((( &( "stack_depth" ) )) # Int  |-> stack_depth_pre)
  **  ((( &( "stack_start" ) )) # Int  |-> stack_start_pre)
  **  ((( &( "sp" ) )) # Int  |-> sp_pre)
|--
  “ (1 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_stack_range_check_safety_wit_4 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ (sp_pre > stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  ((( &( "stack_depth" ) )) # Int  |-> stack_depth_pre)
  **  ((( &( "stack_start" ) )) # Int  |-> stack_start_pre)
  **  ((( &( "sp" ) )) # Int  |-> sp_pre)
|--
  “ (0 <= INT_MAX) ”
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_stack_range_check_return_wit_1 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ (sp_pre > stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  emp
|--
  (“ (0 = 0) ”
  &&  “ (stack_start_pre < sp_pre) ”
  &&  “ (sp_pre <= (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
  ||
  (“ (0 = 1) ”
  &&  “ (sp_pre <= stack_start_pre) ”
  &&  emp)
  ||
  (“ (0 = 1) ”
  &&  “ (sp_pre > (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
.

Definition xizi_stack_range_check_return_wit_2 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre <= stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  emp
|--
  (“ (1 = 0) ”
  &&  “ (stack_start_pre < sp_pre) ”
  &&  “ (sp_pre <= (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ”
  &&  “ (sp_pre <= stack_start_pre) ”
  &&  emp)
  ||
  (“ (1 = 1) ”
  &&  “ (sp_pre > (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
.

Definition xizi_stack_range_check_return_wit_3 :=
forall (stack_depth_pre: Z) (stack_start_pre: Z) (sp_pre: Z) ,
  “ (sp_pre > (stack_start_pre + stack_depth_pre )) ”
  &&  “ (sp_pre > stack_start_pre) ”
  &&  “ (0 <= stack_depth_pre) ”
  &&  “ ((INT_MIN) <= (stack_start_pre + stack_depth_pre )) ”
  &&  “ ((stack_start_pre + stack_depth_pre ) <= INT_MAX) ”
  &&  emp
|--
  (“ (1 = 0) ”
  &&  “ (stack_start_pre < sp_pre) ”
  &&  “ (sp_pre <= (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
  ||
  (“ (1 = 1) ”
  &&  “ (sp_pre <= stack_start_pre) ”
  &&  emp)
  ||
  (“ (1 = 1) ”
  &&  “ (sp_pre > (stack_start_pre + stack_depth_pre )) ”
  &&  emp)
.

Module Type VC_Correct.


Axiom proof_of_xizi_stack_range_check_safety_wit_1 : xizi_stack_range_check_safety_wit_1.
Axiom proof_of_xizi_stack_range_check_safety_wit_2 : xizi_stack_range_check_safety_wit_2.
Axiom proof_of_xizi_stack_range_check_safety_wit_3 : xizi_stack_range_check_safety_wit_3.
Axiom proof_of_xizi_stack_range_check_safety_wit_4 : xizi_stack_range_check_safety_wit_4.
Axiom proof_of_xizi_stack_range_check_return_wit_1 : xizi_stack_range_check_return_wit_1.
Axiom proof_of_xizi_stack_range_check_return_wit_2 : xizi_stack_range_check_return_wit_2.
Axiom proof_of_xizi_stack_range_check_return_wit_3 : xizi_stack_range_check_return_wit_3.

End VC_Correct.
