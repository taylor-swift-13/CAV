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
Require Import ex_allergies_score_count.
Local Open Scope sac.

(*----- Function ex_allergies_score_count -----*)

Definition ex_allergies_score_count_safety_wit_1 := 
forall (score_pre: Z) ,
  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "count" ) )) # Int  |->_)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_allergies_score_count_safety_wit_2 := 
forall (score_pre: Z) ,
  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "count" ) )) # Int  |-> 0)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_allergies_score_count_safety_wit_3 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (8 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 8) ”
.

Definition ex_allergies_score_count_safety_wit_4 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((signed_last_nbits ((1 * (2^i) )) (32)) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (signed_last_nbits ((1 * (2^i) )) (32))) ” 
  &&  “ (i <= 31) ” 
  &&  “ (0 <= i) ”
.

Definition ex_allergies_score_count_safety_wit_5 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition ex_allergies_score_count_safety_wit_6 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_allergies_score_count_safety_wit_7 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ ((Z.land score_pre (signed_last_nbits ((Z.shiftl 1 i)) (32))) <> 0) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((count + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (count + 1 )) ”
.

Definition ex_allergies_score_count_safety_wit_8 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ ((Z.land score_pre (signed_last_nbits ((Z.shiftl 1 i)) (32))) = 0) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> count)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ex_allergies_score_count_safety_wit_9 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ ((Z.land score_pre (signed_last_nbits ((Z.shiftl 1 i)) (32))) <> 0) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "score" ) )) # Int  |-> score_pre)
  **  ((( &( "count" ) )) # Int  |-> (count + 1 ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition ex_allergies_score_count_entail_wit_1 := 
forall (score_pre: Z) ,
  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= 8) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 0) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
.

Definition ex_allergies_score_count_entail_wit_2_1 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ ((Z.land score_pre (signed_last_nbits ((Z.shiftl 1 i)) (32))) <> 0) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= (count + 1 )) ” 
  &&  “ ((count + 1 ) <= (i + 1 )) ” 
  &&  “ ((count + 1 ) = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 (i + 1 )) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
.

Definition ex_allergies_score_count_entail_wit_2_2 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ ((Z.land score_pre (signed_last_nbits ((Z.shiftl 1 i)) (32))) = 0) ” 
  &&  “ (i < 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= (i + 1 )) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 (i + 1 )) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
.

Definition ex_allergies_score_count_entail_wit_3 := 
forall (score_pre: Z) (count: Z) (i: Z) ,
  “ (i >= 8) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count <= i) ” 
  &&  “ (count = (ex_allergies_score_count_spec ((Z.land score_pre ((Z.shiftl 1 i) - 1 ))))) ” 
  &&  “ (0 <= score_pre) ” 
  &&  “ (score_pre <= INT_MAX) ”
  &&  emp
|--
  “ (i = 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count = (ex_allergies_score_count_spec (score_pre))) ”
  &&  emp
.

Definition ex_allergies_score_count_return_wit_1 := 
forall (score_pre: Z) (i: Z) (count: Z) ,
  “ (i = 8) ” 
  &&  “ (0 <= count) ” 
  &&  “ (count = (ex_allergies_score_count_spec (score_pre))) ”
  &&  emp
|--
  “ (0 <= count) ” 
  &&  “ (count <= 8) ” 
  &&  “ (count = (ex_allergies_score_count_spec (score_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_allergies_score_count_safety_wit_1 : ex_allergies_score_count_safety_wit_1.
Axiom proof_of_ex_allergies_score_count_safety_wit_2 : ex_allergies_score_count_safety_wit_2.
Axiom proof_of_ex_allergies_score_count_safety_wit_3 : ex_allergies_score_count_safety_wit_3.
Axiom proof_of_ex_allergies_score_count_safety_wit_4 : ex_allergies_score_count_safety_wit_4.
Axiom proof_of_ex_allergies_score_count_safety_wit_5 : ex_allergies_score_count_safety_wit_5.
Axiom proof_of_ex_allergies_score_count_safety_wit_6 : ex_allergies_score_count_safety_wit_6.
Axiom proof_of_ex_allergies_score_count_safety_wit_7 : ex_allergies_score_count_safety_wit_7.
Axiom proof_of_ex_allergies_score_count_safety_wit_8 : ex_allergies_score_count_safety_wit_8.
Axiom proof_of_ex_allergies_score_count_safety_wit_9 : ex_allergies_score_count_safety_wit_9.
Axiom proof_of_ex_allergies_score_count_entail_wit_1 : ex_allergies_score_count_entail_wit_1.
Axiom proof_of_ex_allergies_score_count_entail_wit_2_1 : ex_allergies_score_count_entail_wit_2_1.
Axiom proof_of_ex_allergies_score_count_entail_wit_2_2 : ex_allergies_score_count_entail_wit_2_2.
Axiom proof_of_ex_allergies_score_count_entail_wit_3 : ex_allergies_score_count_entail_wit_3.
Axiom proof_of_ex_allergies_score_count_return_wit_1 : ex_allergies_score_count_return_wit_1.

End VC_Correct.
