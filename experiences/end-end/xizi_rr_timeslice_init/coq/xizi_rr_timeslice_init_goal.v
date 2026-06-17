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
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function xizi_rr_timeslice_init -----*)

Definition xizi_rr_timeslice_init_safety_wit_1 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  ((( &( "state" ) )) # Ptr  |-> state_pre)
  **  (IntArray.full state_pre 2 l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_rr_timeslice_init_safety_wit_2 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  ((( &( "state" ) )) # Ptr  |-> state_pre)
  **  (IntArray.full state_pre 2 l )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition xizi_rr_timeslice_init_safety_wit_3 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  (IntArray.full state_pre 2 (replace_Znth (0) (10) (l)) )
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_rr_timeslice_init_safety_wit_4 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  (IntArray.full state_pre 2 (replace_Znth (0) (10) (l)) )
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition xizi_rr_timeslice_init_return_wit_1 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  (IntArray.full state_pre 2 (replace_Znth (1) (10) ((replace_Znth (0) (10) (l)))) )
|--
  EX (l0: (@list Z)) ,
  “ ((Zlength (l0)) = 2) ” 
  &&  “ ((Znth 0 l0 0) = 10) ” 
  &&  “ ((Znth 1 l0 0) = 10) ”
  &&  (IntArray.full state_pre 2 l0 )
.

Definition xizi_rr_timeslice_init_partial_solve_wit_1 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  (IntArray.full state_pre 2 l )
|--
  “ ((Zlength (l)) = 2) ”
  &&  (((state_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 0 0 2 l )
.

Definition xizi_rr_timeslice_init_partial_solve_wit_2 := 
forall (state_pre: Z) (l: (@list Z)) ,
  “ ((Zlength (l)) = 2) ”
  &&  (IntArray.full state_pre 2 (replace_Znth (0) (10) (l)) )
|--
  “ ((Zlength (l)) = 2) ”
  &&  (((state_pre + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 1 0 2 (replace_Znth (0) (10) (l)) )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_xizi_rr_timeslice_init_safety_wit_1 : xizi_rr_timeslice_init_safety_wit_1.
Axiom proof_of_xizi_rr_timeslice_init_safety_wit_2 : xizi_rr_timeslice_init_safety_wit_2.
Axiom proof_of_xizi_rr_timeslice_init_safety_wit_3 : xizi_rr_timeslice_init_safety_wit_3.
Axiom proof_of_xizi_rr_timeslice_init_safety_wit_4 : xizi_rr_timeslice_init_safety_wit_4.
Axiom proof_of_xizi_rr_timeslice_init_return_wit_1 : xizi_rr_timeslice_init_return_wit_1.
Axiom proof_of_xizi_rr_timeslice_init_partial_solve_wit_1 : xizi_rr_timeslice_init_partial_solve_wit_1.
Axiom proof_of_xizi_rr_timeslice_init_partial_solve_wit_2 : xizi_rr_timeslice_init_partial_solve_wit_2.

End VC_Correct.
