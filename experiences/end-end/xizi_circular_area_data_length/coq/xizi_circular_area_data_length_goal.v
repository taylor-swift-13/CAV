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

(*----- Function xizi_circular_area_data_length -----*)

Definition xizi_circular_area_data_length_safety_wit_1 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (readidx_pre = writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_circular_area_data_length_safety_wit_2 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre < readidx_pre) ” 
  &&  “ (status_pre = 0) ” 
  &&  “ (readidx_pre = writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ False ”
.

Definition xizi_circular_area_data_length_safety_wit_3 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre >= readidx_pre) ” 
  &&  “ (status_pre = 0) ” 
  &&  “ (readidx_pre = writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ ((writeidx_pre - readidx_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (writeidx_pre - readidx_pre )) ”
.

Definition xizi_circular_area_data_length_safety_wit_4 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre >= readidx_pre) ” 
  &&  “ (readidx_pre <> writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ ((writeidx_pre - readidx_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (writeidx_pre - readidx_pre )) ”
.

Definition xizi_circular_area_data_length_safety_wit_5 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre < readidx_pre) ” 
  &&  “ (readidx_pre <> writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ ((area_length_pre - (readidx_pre - writeidx_pre ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (area_length_pre - (readidx_pre - writeidx_pre ) )) ”
.

Definition xizi_circular_area_data_length_safety_wit_6 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre < readidx_pre) ” 
  &&  “ (readidx_pre <> writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "status" ) )) # Int  |-> status_pre)
  **  ((( &( "writeidx" ) )) # Int  |-> writeidx_pre)
  **  ((( &( "readidx" ) )) # Int  |-> readidx_pre)
|--
  “ ((readidx_pre - writeidx_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (readidx_pre - writeidx_pre )) ”
.

Definition xizi_circular_area_data_length_return_wit_1 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre < readidx_pre) ” 
  &&  “ (readidx_pre <> writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  emp
|--
  “ (((readidx_pre = writeidx_pre) /\ (status_pre <> 0)) -> ((area_length_pre - (readidx_pre - writeidx_pre ) ) = area_length_pre)) ” 
  &&  “ (((readidx_pre = writeidx_pre) /\ (status_pre = 0)) -> ((area_length_pre - (readidx_pre - writeidx_pre ) ) = 0)) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre >= readidx_pre)) -> ((area_length_pre - (readidx_pre - writeidx_pre ) ) = (writeidx_pre - readidx_pre ))) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre < readidx_pre)) -> ((area_length_pre - (readidx_pre - writeidx_pre ) ) = (area_length_pre - (readidx_pre - writeidx_pre ) ))) ”
  &&  emp
.

Definition xizi_circular_area_data_length_return_wit_2 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre >= readidx_pre) ” 
  &&  “ (status_pre = 0) ” 
  &&  “ (readidx_pre = writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  emp
|--
  “ (((readidx_pre = writeidx_pre) /\ (status_pre <> 0)) -> ((writeidx_pre - readidx_pre ) = area_length_pre)) ” 
  &&  “ (((readidx_pre = writeidx_pre) /\ (status_pre = 0)) -> ((writeidx_pre - readidx_pre ) = 0)) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre >= readidx_pre)) -> ((writeidx_pre - readidx_pre ) = (writeidx_pre - readidx_pre ))) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre < readidx_pre)) -> ((writeidx_pre - readidx_pre ) = (area_length_pre - (readidx_pre - writeidx_pre ) ))) ”
  &&  emp
.

Definition xizi_circular_area_data_length_return_wit_3 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (writeidx_pre >= readidx_pre) ” 
  &&  “ (readidx_pre <> writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  emp
|--
  “ (((readidx_pre = writeidx_pre) /\ (status_pre <> 0)) -> ((writeidx_pre - readidx_pre ) = area_length_pre)) ” 
  &&  “ (((readidx_pre = writeidx_pre) /\ (status_pre = 0)) -> ((writeidx_pre - readidx_pre ) = 0)) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre >= readidx_pre)) -> ((writeidx_pre - readidx_pre ) = (writeidx_pre - readidx_pre ))) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre < readidx_pre)) -> ((writeidx_pre - readidx_pre ) = (area_length_pre - (readidx_pre - writeidx_pre ) ))) ”
  &&  emp
.

Definition xizi_circular_area_data_length_return_wit_4 := 
forall (area_length_pre: Z) (status_pre: Z) (writeidx_pre: Z) (readidx_pre: Z) ,
  “ (status_pre <> 0) ” 
  &&  “ (readidx_pre = writeidx_pre) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (0 <= readidx_pre) ” 
  &&  “ (readidx_pre < area_length_pre) ” 
  &&  “ (0 <= writeidx_pre) ” 
  &&  “ (writeidx_pre < area_length_pre) ”
  &&  emp
|--
  “ (((readidx_pre = writeidx_pre) /\ (status_pre <> 0)) -> (area_length_pre = area_length_pre)) ” 
  &&  “ (((readidx_pre = writeidx_pre) /\ (status_pre = 0)) -> (area_length_pre = 0)) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre >= readidx_pre)) -> (area_length_pre = (writeidx_pre - readidx_pre ))) ” 
  &&  “ (((readidx_pre <> writeidx_pre) /\ (writeidx_pre < readidx_pre)) -> (area_length_pre = (area_length_pre - (readidx_pre - writeidx_pre ) ))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_xizi_circular_area_data_length_safety_wit_1 : xizi_circular_area_data_length_safety_wit_1.
Axiom proof_of_xizi_circular_area_data_length_safety_wit_2 : xizi_circular_area_data_length_safety_wit_2.
Axiom proof_of_xizi_circular_area_data_length_safety_wit_3 : xizi_circular_area_data_length_safety_wit_3.
Axiom proof_of_xizi_circular_area_data_length_safety_wit_4 : xizi_circular_area_data_length_safety_wit_4.
Axiom proof_of_xizi_circular_area_data_length_safety_wit_5 : xizi_circular_area_data_length_safety_wit_5.
Axiom proof_of_xizi_circular_area_data_length_safety_wit_6 : xizi_circular_area_data_length_safety_wit_6.
Axiom proof_of_xizi_circular_area_data_length_return_wit_1 : xizi_circular_area_data_length_return_wit_1.
Axiom proof_of_xizi_circular_area_data_length_return_wit_2 : xizi_circular_area_data_length_return_wit_2.
Axiom proof_of_xizi_circular_area_data_length_return_wit_3 : xizi_circular_area_data_length_return_wit_3.
Axiom proof_of_xizi_circular_area_data_length_return_wit_4 : xizi_circular_area_data_length_return_wit_4.

End VC_Correct.
