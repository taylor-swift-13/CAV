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

(*----- Function xizi_ready_highest_prio_update -----*)

Definition xizi_ready_highest_prio_update_return_wit_1 := 
forall (task_prio_pre: Z) (current_highest_pre: Z) ,
  “ (task_prio_pre > current_highest_pre) ”
  &&  emp
|--
  “ ((task_prio_pre > current_highest_pre) -> (task_prio_pre = task_prio_pre)) ” 
  &&  “ ((task_prio_pre <= current_highest_pre) -> (task_prio_pre = current_highest_pre)) ”
  &&  emp
.

Definition xizi_ready_highest_prio_update_return_wit_2 := 
forall (task_prio_pre: Z) (current_highest_pre: Z) ,
  “ (task_prio_pre <= current_highest_pre) ”
  &&  emp
|--
  “ ((task_prio_pre > current_highest_pre) -> (current_highest_pre = task_prio_pre)) ” 
  &&  “ ((task_prio_pre <= current_highest_pre) -> (current_highest_pre = current_highest_pre)) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_xizi_ready_highest_prio_update_return_wit_1 : xizi_ready_highest_prio_update_return_wit_1.
Axiom proof_of_xizi_ready_highest_prio_update_return_wit_2 : xizi_ready_highest_prio_update_return_wit_2.

End VC_Correct.
