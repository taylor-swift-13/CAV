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
Require Import xizi_bitmap_highest_prio.
Local Open Scope sac.

(*----- Function xizi_bitmap_highest_prio -----*)

Definition xizi_bitmap_highest_prio_safety_wit_1 := 
forall (bitmap_pre: Z) ,
  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ”
  &&  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
  **  ((( &( "i" ) )) # Int  |->_)
|--
  “ (31 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 31) ”
.

Definition xizi_bitmap_highest_prio_safety_wit_2 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_bitmap_highest_prio_safety_wit_3 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
|--
  “ (i <= 31) ” 
  &&  “ (0 <= i) ”
.

Definition xizi_bitmap_highest_prio_safety_wit_4 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ ((Z.land bitmap_pre (Z.shiftl 1 i)) = 0) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
|--
  “ ((i - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i - 1 )) ”
.

Definition xizi_bitmap_highest_prio_safety_wit_5 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_bitmap_highest_prio_entail_wit_1 := 
forall (bitmap_pre: Z) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
|--
  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ”
  &&  ((( &( "bitmap" ) )) # UInt  |-> bitmap_pre)
  **  ((( &( "i" ) )) # Int  |->_)
.

Definition xizi_bitmap_highest_prio_entail_wit_2 := 
forall (bitmap_pre: Z) ,
  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ”
  &&  emp
|--
  “ ((-1) <= 31) ” 
  &&  “ (31 <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((31 < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  emp
.

Definition xizi_bitmap_highest_prio_entail_wit_3 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ ((Z.land bitmap_pre (Z.shiftl 1 i)) = 0) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  emp
|--
  “ ((-1) <= (i - 1 )) ” 
  &&  “ ((i - 1 ) <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , ((((i - 1 ) < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  emp
.

Definition xizi_bitmap_highest_prio_return_wit_1 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ (i < 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  emp
|--
  “ (xizi_bitmap_highest_prio_spec bitmap_pre 0 ) ”
  &&  emp
.

Definition xizi_bitmap_highest_prio_return_wit_2 := 
forall (bitmap_pre: Z) (i: Z) ,
  “ ((Z.land bitmap_pre (Z.shiftl 1 i)) <> 0) ” 
  &&  “ (i >= 0) ” 
  &&  “ ((-1) <= i) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= bitmap_pre) ” 
  &&  “ (bitmap_pre <= UINT_MAX) ” 
  &&  “ forall (k: Z) , (((i < k) /\ (k < 32)) -> ((Z.land (Z.shiftr bitmap_pre k) 1) = 0)) ”
  &&  emp
|--
  “ (xizi_bitmap_highest_prio_spec bitmap_pre i ) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_xizi_bitmap_highest_prio_safety_wit_1 : xizi_bitmap_highest_prio_safety_wit_1.
Axiom proof_of_xizi_bitmap_highest_prio_safety_wit_2 : xizi_bitmap_highest_prio_safety_wit_2.
Axiom proof_of_xizi_bitmap_highest_prio_safety_wit_3 : xizi_bitmap_highest_prio_safety_wit_3.
Axiom proof_of_xizi_bitmap_highest_prio_safety_wit_4 : xizi_bitmap_highest_prio_safety_wit_4.
Axiom proof_of_xizi_bitmap_highest_prio_safety_wit_5 : xizi_bitmap_highest_prio_safety_wit_5.
Axiom proof_of_xizi_bitmap_highest_prio_entail_wit_1 : xizi_bitmap_highest_prio_entail_wit_1.
Axiom proof_of_xizi_bitmap_highest_prio_entail_wit_2 : xizi_bitmap_highest_prio_entail_wit_2.
Axiom proof_of_xizi_bitmap_highest_prio_entail_wit_3 : xizi_bitmap_highest_prio_entail_wit_3.
Axiom proof_of_xizi_bitmap_highest_prio_return_wit_1 : xizi_bitmap_highest_prio_return_wit_1.
Axiom proof_of_xizi_bitmap_highest_prio_return_wit_2 : xizi_bitmap_highest_prio_return_wit_2.

End VC_Correct.
