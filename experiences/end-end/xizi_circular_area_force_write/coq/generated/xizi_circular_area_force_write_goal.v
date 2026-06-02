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

(*----- Function xizi_circular_area_force_write -----*)

Definition xizi_circular_area_force_write_safety_wit_1 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  ((( &( "writeidx" ) )) # Int  |->_)
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
  **  (IntArray.full state_pre 3 l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_circular_area_force_write_safety_wit_2 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (((Znth 1 l 0) + data_length_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 l 0) + data_length_pre )) ”
.

Definition xizi_circular_area_force_write_safety_wit_3 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ ((((Znth 1 l 0) + data_length_pre ) <> (INT_MIN)) \/ (area_length_pre <> (-1))) ” 
  &&  “ (area_length_pre <> 0) ”
.

Definition xizi_circular_area_force_write_safety_wit_4 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (((Znth 1 l 0) + data_length_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((Znth 1 l 0) + data_length_pre )) ”
.

Definition xizi_circular_area_force_write_safety_wit_5 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) ”
.

Definition xizi_circular_area_force_write_safety_wit_6 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (Znth 1 l 0))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ ((area_length_pre - (Znth 1 l 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (area_length_pre - (Znth 1 l 0) )) ”
.

Definition xizi_circular_area_force_write_safety_wit_7 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (data_length_pre - (area_length_pre - (Znth 1 l 0) ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_circular_area_force_write_safety_wit_8 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
  **  ((( &( "writeidx" ) )) # Int  |-> (((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_circular_area_force_write_safety_wit_9 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)) )
  **  ((( &( "writeidx" ) )) # Int  |-> (((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition xizi_circular_area_force_write_safety_wit_10 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)) )
  **  ((( &( "writeidx" ) )) # Int  |-> (data_length_pre - (area_length_pre - (Znth 1 l 0) ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition xizi_circular_area_force_write_safety_wit_11 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)) )
  **  ((( &( "writeidx" ) )) # Int  |-> (((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_circular_area_force_write_safety_wit_12 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)) )
  **  ((( &( "writeidx" ) )) # Int  |-> (data_length_pre - (area_length_pre - (Znth 1 l 0) ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_circular_area_force_write_safety_wit_13 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))) )
  **  ((( &( "writeidx" ) )) # Int  |-> (data_length_pre - (area_length_pre - (Znth 1 l 0) ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_circular_area_force_write_safety_wit_14 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))) )
  **  ((( &( "writeidx" ) )) # Int  |-> (((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_circular_area_force_write_safety_wit_15 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))) )
  **  ((( &( "writeidx" ) )) # Int  |-> (((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_circular_area_force_write_safety_wit_16 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))) )
  **  ((( &( "writeidx" ) )) # Int  |-> (data_length_pre - (area_length_pre - (Znth 1 l 0) ) ))
  **  ((( &( "force" ) )) # Int  |-> force_pre)
  **  ((( &( "area_length" ) )) # Int  |-> area_length_pre)
  **  ((( &( "data_length" ) )) # Int  |-> data_length_pre)
  **  ((( &( "state" ) )) # Ptr  |-> state_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_circular_area_force_write_return_wit_1 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (0) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) ((replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))))) )
|--
  EX (lr: (@list Z)) ,
  “ ((Zlength (lr)) = 3) ” 
  &&  “ (0 <= (Znth 1 lr 0)) ” 
  &&  “ ((Znth 1 lr 0) < area_length_pre) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) < area_length_pre) -> ((Znth 1 lr 0) = ((Znth 1 l 0) + data_length_pre ))) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) = area_length_pre) -> ((Znth 1 lr 0) = 0)) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) > area_length_pre) -> ((Znth 1 lr 0) = (((Znth 1 l 0) + data_length_pre ) - area_length_pre ))) ” 
  &&  “ ((Znth 2 lr 0) = 1) ” 
  &&  “ ((force_pre <> 0) -> ((Znth 0 lr 0) = (Znth 1 lr 0))) ” 
  &&  “ ((force_pre = 0) -> ((Znth 0 lr 0) = (Znth 0 l 0))) ”
  &&  (IntArray.full state_pre 3 lr )
.

Definition xizi_circular_area_force_write_return_wit_2 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (0) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) ((replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))))) )
|--
  EX (lr: (@list Z)) ,
  “ ((Zlength (lr)) = 3) ” 
  &&  “ (0 <= (Znth 1 lr 0)) ” 
  &&  “ ((Znth 1 lr 0) < area_length_pre) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) < area_length_pre) -> ((Znth 1 lr 0) = ((Znth 1 l 0) + data_length_pre ))) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) = area_length_pre) -> ((Znth 1 lr 0) = 0)) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) > area_length_pre) -> ((Znth 1 lr 0) = (((Znth 1 l 0) + data_length_pre ) - area_length_pre ))) ” 
  &&  “ ((Znth 2 lr 0) = 1) ” 
  &&  “ ((force_pre <> 0) -> ((Znth 0 lr 0) = (Znth 1 lr 0))) ” 
  &&  “ ((force_pre = 0) -> ((Znth 0 lr 0) = (Znth 0 l 0))) ”
  &&  (IntArray.full state_pre 3 lr )
.

Definition xizi_circular_area_force_write_return_wit_3 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre = 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))) )
|--
  EX (lr: (@list Z)) ,
  “ ((Zlength (lr)) = 3) ” 
  &&  “ (0 <= (Znth 1 lr 0)) ” 
  &&  “ ((Znth 1 lr 0) < area_length_pre) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) < area_length_pre) -> ((Znth 1 lr 0) = ((Znth 1 l 0) + data_length_pre ))) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) = area_length_pre) -> ((Znth 1 lr 0) = 0)) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) > area_length_pre) -> ((Znth 1 lr 0) = (((Znth 1 l 0) + data_length_pre ) - area_length_pre ))) ” 
  &&  “ ((Znth 2 lr 0) = 1) ” 
  &&  “ ((force_pre <> 0) -> ((Znth 0 lr 0) = (Znth 1 lr 0))) ” 
  &&  “ ((force_pre = 0) -> ((Znth 0 lr 0) = (Znth 0 l 0))) ”
  &&  (IntArray.full state_pre 3 lr )
.

Definition xizi_circular_area_force_write_return_wit_4 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre = 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))) )
|--
  EX (lr: (@list Z)) ,
  “ ((Zlength (lr)) = 3) ” 
  &&  “ (0 <= (Znth 1 lr 0)) ” 
  &&  “ ((Znth 1 lr 0) < area_length_pre) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) < area_length_pre) -> ((Znth 1 lr 0) = ((Znth 1 l 0) + data_length_pre ))) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) = area_length_pre) -> ((Znth 1 lr 0) = 0)) ” 
  &&  “ ((((Znth 1 l 0) + data_length_pre ) > area_length_pre) -> ((Znth 1 lr 0) = (((Znth 1 l 0) + data_length_pre ) - area_length_pre ))) ” 
  &&  “ ((Znth 2 lr 0) = 1) ” 
  &&  “ ((force_pre <> 0) -> ((Znth 0 lr 0) = (Znth 1 lr 0))) ” 
  &&  “ ((force_pre = 0) -> ((Znth 0 lr 0) = (Znth 0 l 0))) ”
  &&  (IntArray.full state_pre 3 lr )
.

Definition xizi_circular_area_force_write_partial_solve_wit_1 := 
forall (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
|--
  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (1 * sizeof(INT) ) )) # Int  |-> (Znth 1 l 0))
  **  (IntArray.missing_i state_pre 1 0 3 l )
.

Definition xizi_circular_area_force_write_partial_solve_wit_2 := 
forall (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
|--
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 1 0 3 l )
.

Definition xizi_circular_area_force_write_partial_solve_wit_3 := 
forall (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 l )
|--
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (1 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 1 0 3 l )
.

Definition xizi_circular_area_force_write_partial_solve_wit_4 := 
forall (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)) )
|--
  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 2 0 3 (replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)) )
.

Definition xizi_circular_area_force_write_partial_solve_wit_5 := 
forall (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)) )
|--
  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (2 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 2 0 3 (replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)) )
.

Definition xizi_circular_area_force_write_partial_solve_wit_6 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))) )
|--
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) <= area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 0 0 3 (replace_Znth (2) (1) ((replace_Znth (1) ((((Znth 1 l 0) + data_length_pre ) % ( area_length_pre ) )) (l)))) )
.

Definition xizi_circular_area_force_write_partial_solve_wit_7 := 
forall (force_pre: Z) (area_length_pre: Z) (data_length_pre: Z) (state_pre: Z) (l: (@list Z)) ,
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (IntArray.full state_pre 3 (replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))) )
|--
  “ (force_pre <> 0) ” 
  &&  “ (((Znth 1 l 0) + data_length_pre ) > area_length_pre) ” 
  &&  “ (state_pre <> 0) ” 
  &&  “ (0 < area_length_pre) ” 
  &&  “ (area_length_pre <= 1073741824) ” 
  &&  “ ((Zlength (l)) = 3) ” 
  &&  “ (0 <= (Znth 0 l 0)) ” 
  &&  “ ((Znth 0 l 0) < area_length_pre) ” 
  &&  “ (0 <= (Znth 1 l 0)) ” 
  &&  “ ((Znth 1 l 0) < area_length_pre) ” 
  &&  “ (0 <= data_length_pre) ” 
  &&  “ (data_length_pre <= area_length_pre) ”
  &&  (((state_pre + (0 * sizeof(INT) ) )) # Int  |->_)
  **  (IntArray.missing_i state_pre 0 0 3 (replace_Znth (2) (1) ((replace_Znth (1) ((data_length_pre - (area_length_pre - (Znth 1 l 0) ) )) (l)))) )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_xizi_circular_area_force_write_safety_wit_1 : xizi_circular_area_force_write_safety_wit_1.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_2 : xizi_circular_area_force_write_safety_wit_2.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_3 : xizi_circular_area_force_write_safety_wit_3.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_4 : xizi_circular_area_force_write_safety_wit_4.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_5 : xizi_circular_area_force_write_safety_wit_5.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_6 : xizi_circular_area_force_write_safety_wit_6.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_7 : xizi_circular_area_force_write_safety_wit_7.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_8 : xizi_circular_area_force_write_safety_wit_8.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_9 : xizi_circular_area_force_write_safety_wit_9.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_10 : xizi_circular_area_force_write_safety_wit_10.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_11 : xizi_circular_area_force_write_safety_wit_11.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_12 : xizi_circular_area_force_write_safety_wit_12.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_13 : xizi_circular_area_force_write_safety_wit_13.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_14 : xizi_circular_area_force_write_safety_wit_14.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_15 : xizi_circular_area_force_write_safety_wit_15.
Axiom proof_of_xizi_circular_area_force_write_safety_wit_16 : xizi_circular_area_force_write_safety_wit_16.
Axiom proof_of_xizi_circular_area_force_write_return_wit_1 : xizi_circular_area_force_write_return_wit_1.
Axiom proof_of_xizi_circular_area_force_write_return_wit_2 : xizi_circular_area_force_write_return_wit_2.
Axiom proof_of_xizi_circular_area_force_write_return_wit_3 : xizi_circular_area_force_write_return_wit_3.
Axiom proof_of_xizi_circular_area_force_write_return_wit_4 : xizi_circular_area_force_write_return_wit_4.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_1 : xizi_circular_area_force_write_partial_solve_wit_1.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_2 : xizi_circular_area_force_write_partial_solve_wit_2.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_3 : xizi_circular_area_force_write_partial_solve_wit_3.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_4 : xizi_circular_area_force_write_partial_solve_wit_4.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_5 : xizi_circular_area_force_write_partial_solve_wit_5.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_6 : xizi_circular_area_force_write_partial_solve_wit_6.
Axiom proof_of_xizi_circular_area_force_write_partial_solve_wit_7 : xizi_circular_area_force_write_partial_solve_wit_7.

End VC_Correct.
