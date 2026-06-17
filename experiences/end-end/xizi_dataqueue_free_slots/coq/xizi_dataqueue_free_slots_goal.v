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

(*----- Function xizi_dataqueue_free_slots -----*)

Definition xizi_dataqueue_free_slots_safety_wit_1 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |->_)
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ ((((rear_pre - front_pre ) + max_len_pre ) <> (INT_MIN)) \/ (max_len_pre <> (-1))) ” 
  &&  “ (max_len_pre <> 0) ”
.

Definition xizi_dataqueue_free_slots_safety_wit_2 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |->_)
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ (((rear_pre - front_pre ) + max_len_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((rear_pre - front_pre ) + max_len_pre )) ”
.

Definition xizi_dataqueue_free_slots_safety_wit_3 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |->_)
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ ((rear_pre - front_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (rear_pre - front_pre )) ”
.

Definition xizi_dataqueue_free_slots_safety_wit_4 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |-> (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ))
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ (((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) )) ”
.

Definition xizi_dataqueue_free_slots_safety_wit_5 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |-> (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ))
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ ((max_len_pre - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (max_len_pre - 1 )) ”
.

Definition xizi_dataqueue_free_slots_safety_wit_6 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  ((( &( "used" ) )) # Int  |-> (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ))
  **  ((( &( "max_len" ) )) # Int  |-> max_len_pre)
  **  ((( &( "rear" ) )) # Int  |-> rear_pre)
  **  ((( &( "front" ) )) # Int  |-> front_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_dataqueue_free_slots_return_wit_1 := 
forall (max_len_pre: Z) (rear_pre: Z) (front_pre: Z) ,
  “ (1 < max_len_pre) ” 
  &&  “ (max_len_pre <= 1073741824) ” 
  &&  “ (0 <= front_pre) ” 
  &&  “ (front_pre < max_len_pre) ” 
  &&  “ (0 <= rear_pre) ” 
  &&  “ (rear_pre < max_len_pre) ”
  &&  emp
|--
  “ (0 <= ((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) )) ” 
  &&  “ (((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) ) < max_len_pre) ” 
  &&  “ ((front_pre <= rear_pre) -> (((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) ) = ((max_len_pre - 1 ) - (rear_pre - front_pre ) ))) ” 
  &&  “ ((rear_pre < front_pre) -> (((max_len_pre - 1 ) - (((rear_pre - front_pre ) + max_len_pre ) % ( max_len_pre ) ) ) = ((front_pre - rear_pre ) - 1 ))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_1 : xizi_dataqueue_free_slots_safety_wit_1.
Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_2 : xizi_dataqueue_free_slots_safety_wit_2.
Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_3 : xizi_dataqueue_free_slots_safety_wit_3.
Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_4 : xizi_dataqueue_free_slots_safety_wit_4.
Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_5 : xizi_dataqueue_free_slots_safety_wit_5.
Axiom proof_of_xizi_dataqueue_free_slots_safety_wit_6 : xizi_dataqueue_free_slots_safety_wit_6.
Axiom proof_of_xizi_dataqueue_free_slots_return_wit_1 : xizi_dataqueue_free_slots_return_wit_1.

End VC_Correct.
