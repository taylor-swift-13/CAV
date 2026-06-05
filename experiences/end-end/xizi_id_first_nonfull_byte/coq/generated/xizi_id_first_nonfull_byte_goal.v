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

(*----- Function xizi_id_first_nonfull_byte -----*)

Definition xizi_id_first_nonfull_byte_safety_wit_1 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  (IntArray.full id_map_pre n_pre l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_id_first_nonfull_byte_safety_wit_2 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
|--
  “ (255 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 255) ”
.

Definition xizi_id_first_nonfull_byte_safety_wit_3 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
|--
  “ (255 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 255) ”
.

Definition xizi_id_first_nonfull_byte_safety_wit_4 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ ((Z.land (Znth i l 0) 255) = 255) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition xizi_id_first_nonfull_byte_safety_wit_5 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
  **  (IntArray.full id_map_pre n_pre l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition xizi_id_first_nonfull_byte_safety_wit_6 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "id_map" ) )) # Ptr  |-> id_map_pre)
  **  (IntArray.full id_map_pre n_pre l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_id_first_nonfull_byte_entail_wit_1 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < 0)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
.

Definition xizi_id_first_nonfull_byte_entail_wit_2 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ ((Z.land (Znth i l 0) 255) = 255) ” 
  &&  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < (i + 1 ))) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
.

Definition xizi_id_first_nonfull_byte_return_wit_1 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i_3: Z) ,
  “ (i_3 >= n_pre) ” 
  &&  “ (0 <= i_3) ” 
  &&  “ (i_3 <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i_3)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
|--
  (“ (0 <= (-1)) ” 
  &&  “ ((-1) < n_pre) ” 
  &&  “ ((Z.land (Znth (-1) l 0) 255) <> 255) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < (-1))) -> ((Z.land (Znth i l 0) 255) = 255)) ”
  &&  (IntArray.full id_map_pre n_pre l ))
  ||
  (“ ((-1) = (-1)) ” 
  &&  “ forall (i_2: Z) , (((0 <= i_2) /\ (i_2 < n_pre)) -> ((Z.land (Znth i_2 l 0) 255) = 255)) ”
  &&  (IntArray.full id_map_pre n_pre l ))
.

Definition xizi_id_first_nonfull_byte_return_wit_2 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i_2: Z) ,
  “ ((Z.land (Znth i_2 l 0) 255) <> 255) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ (0 <= i_2) ” 
  &&  “ (i_2 <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i_2)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
|--
  (“ (0 <= i_2) ” 
  &&  “ (i_2 < n_pre) ” 
  &&  “ ((Z.land (Znth i_2 l 0) 255) <> 255) ” 
  &&  “ forall (i: Z) , (((0 <= i) /\ (i < i_2)) -> ((Z.land (Znth i l 0) 255) = 255)) ”
  &&  (IntArray.full id_map_pre n_pre l ))
  ||
  (“ (i_2 = (-1)) ” 
  &&  “ forall (i_3: Z) , (((0 <= i_3) /\ (i_3 < n_pre)) -> ((Z.land (Znth i_3 l 0) 255) = 255)) ”
  &&  (IntArray.full id_map_pre n_pre l ))
.

Definition xizi_id_first_nonfull_byte_partial_solve_wit_1 := 
forall (id_map_pre: Z) (n_pre: Z) (l: (@list Z)) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (IntArray.full id_map_pre n_pre l )
|--
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ forall (j: Z) , (((0 <= j) /\ (j < i)) -> ((Z.land (Znth j l 0) 255) = 255)) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ ((Zlength (l)) = n_pre) ”
  &&  (((id_map_pre + (i * sizeof(INT) ) )) # Int  |-> (Znth i l 0))
  **  (IntArray.missing_i id_map_pre i 0 n_pre l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_1 : xizi_id_first_nonfull_byte_safety_wit_1.
Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_2 : xizi_id_first_nonfull_byte_safety_wit_2.
Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_3 : xizi_id_first_nonfull_byte_safety_wit_3.
Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_4 : xizi_id_first_nonfull_byte_safety_wit_4.
Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_5 : xizi_id_first_nonfull_byte_safety_wit_5.
Axiom proof_of_xizi_id_first_nonfull_byte_safety_wit_6 : xizi_id_first_nonfull_byte_safety_wit_6.
Axiom proof_of_xizi_id_first_nonfull_byte_entail_wit_1 : xizi_id_first_nonfull_byte_entail_wit_1.
Axiom proof_of_xizi_id_first_nonfull_byte_entail_wit_2 : xizi_id_first_nonfull_byte_entail_wit_2.
Axiom proof_of_xizi_id_first_nonfull_byte_return_wit_1 : xizi_id_first_nonfull_byte_return_wit_1.
Axiom proof_of_xizi_id_first_nonfull_byte_return_wit_2 : xizi_id_first_nonfull_byte_return_wit_2.
Axiom proof_of_xizi_id_first_nonfull_byte_partial_solve_wit_1 : xizi_id_first_nonfull_byte_partial_solve_wit_1.

End VC_Correct.
