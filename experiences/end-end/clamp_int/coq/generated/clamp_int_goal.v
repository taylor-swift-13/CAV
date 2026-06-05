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

(*----- Function clamp_int -----*)

Definition clamp_int_return_wit_1 := 
forall (hi_pre: Z) (lo_pre: Z) (x_pre: Z) ,
  “ (x_pre <= hi_pre) ” 
  &&  “ (x_pre >= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ”
  &&  emp
|--
  “ ((x_pre < lo_pre) -> (x_pre = lo_pre)) ” 
  &&  “ ((x_pre > hi_pre) -> (x_pre = hi_pre)) ” 
  &&  “ (((lo_pre <= x_pre) /\ (x_pre <= hi_pre)) -> (x_pre = x_pre)) ”
  &&  emp
.

Definition clamp_int_return_wit_2 := 
forall (hi_pre: Z) (lo_pre: Z) (x_pre: Z) ,
  “ (x_pre > hi_pre) ” 
  &&  “ (x_pre >= lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ”
  &&  emp
|--
  “ ((x_pre < lo_pre) -> (hi_pre = lo_pre)) ” 
  &&  “ ((x_pre > hi_pre) -> (hi_pre = hi_pre)) ” 
  &&  “ (((lo_pre <= x_pre) /\ (x_pre <= hi_pre)) -> (hi_pre = x_pre)) ”
  &&  emp
.

Definition clamp_int_return_wit_3 := 
forall (hi_pre: Z) (lo_pre: Z) (x_pre: Z) ,
  “ (x_pre < lo_pre) ” 
  &&  “ (lo_pre <= hi_pre) ”
  &&  emp
|--
  “ ((x_pre < lo_pre) -> (lo_pre = lo_pre)) ” 
  &&  “ ((x_pre > hi_pre) -> (lo_pre = hi_pre)) ” 
  &&  “ (((lo_pre <= x_pre) /\ (x_pre <= hi_pre)) -> (lo_pre = x_pre)) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_clamp_int_return_wit_1 : clamp_int_return_wit_1.
Axiom proof_of_clamp_int_return_wit_2 : clamp_int_return_wit_2.
Axiom proof_of_clamp_int_return_wit_3 : clamp_int_return_wit_3.

End VC_Correct.
