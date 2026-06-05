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
Require Import arithmetic_series.
Local Open Scope sac.

(*----- Function arithmetic_series -----*)

Definition arithmetic_series_safety_wit_1 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) ,
  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arithmetic_series_safety_wit_2 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) ,
  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  ((( &( "sum" ) )) # Int  |->_)
  **  ((( &( "cur" ) )) # Int  |-> a_pre)
  **  ((( &( "i" ) )) # Int  |-> 0)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition arithmetic_series_safety_wit_3 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) (sum: Z) (cur: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cur = (a_pre + (i * d_pre ) )) ” 
  &&  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (i))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "sum" ) )) # Int  |-> sum)
|--
  “ ((sum + cur ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (sum + cur )) ”
.

Definition arithmetic_series_safety_wit_4 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) (sum: Z) (cur: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cur = (a_pre + (i * d_pre ) )) ” 
  &&  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (i))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "cur" ) )) # Int  |-> cur)
  **  ((( &( "sum" ) )) # Int  |-> (sum + cur ))
|--
  “ ((cur + d_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (cur + d_pre )) ”
.

Definition arithmetic_series_safety_wit_5 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) (sum: Z) (cur: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cur = (a_pre + (i * d_pre ) )) ” 
  &&  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (i))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "a" ) )) # Int  |-> a_pre)
  **  ((( &( "d" ) )) # Int  |-> d_pre)
  **  ((( &( "cur" ) )) # Int  |-> (cur + d_pre ))
  **  ((( &( "sum" ) )) # Int  |-> (sum + cur ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition arithmetic_series_entail_wit_1 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) ,
  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  emp
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (a_pre = (a_pre + (0 * d_pre ) )) ” 
  &&  “ (0 = (arithmetic_series_sum_z (a_pre) (d_pre) (0))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  emp
.

Definition arithmetic_series_entail_wit_2 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) (sum: Z) (cur: Z) (i: Z) ,
  “ (i < n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cur = (a_pre + (i * d_pre ) )) ” 
  &&  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (i))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  emp
|--
  “ (0 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= n_pre) ” 
  &&  “ ((cur + d_pre ) = (a_pre + ((i + 1 ) * d_pre ) )) ” 
  &&  “ ((sum + cur ) = (arithmetic_series_sum_z (a_pre) (d_pre) ((i + 1 )))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  emp
.

Definition arithmetic_series_return_wit_1 := 
forall (n_pre: Z) (d_pre: Z) (a_pre: Z) (sum: Z) (cur: Z) (i: Z) ,
  “ (i >= n_pre) ” 
  &&  “ (0 <= i) ” 
  &&  “ (i <= n_pre) ” 
  &&  “ (cur = (a_pre + (i * d_pre ) )) ” 
  &&  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (i))) ” 
  &&  “ (arithmetic_series_pre a_pre d_pre n_pre ) ”
  &&  emp
|--
  “ (sum = (arithmetic_series_sum_z (a_pre) (d_pre) (n_pre))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_arithmetic_series_safety_wit_1 : arithmetic_series_safety_wit_1.
Axiom proof_of_arithmetic_series_safety_wit_2 : arithmetic_series_safety_wit_2.
Axiom proof_of_arithmetic_series_safety_wit_3 : arithmetic_series_safety_wit_3.
Axiom proof_of_arithmetic_series_safety_wit_4 : arithmetic_series_safety_wit_4.
Axiom proof_of_arithmetic_series_safety_wit_5 : arithmetic_series_safety_wit_5.
Axiom proof_of_arithmetic_series_entail_wit_1 : arithmetic_series_entail_wit_1.
Axiom proof_of_arithmetic_series_entail_wit_2 : arithmetic_series_entail_wit_2.
Axiom proof_of_arithmetic_series_return_wit_1 : arithmetic_series_return_wit_1.

End VC_Correct.
