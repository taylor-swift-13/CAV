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
Require Import xizi_single_link_lib.
Local Open Scope sac.

(*----- Function xizi_single_link_init -----*)

Definition xizi_single_link_init_safety_wit_1 := 
forall (linklist_pre: Z) (first: Z) ,
  “ (linklist_pre <> 0) ”
  &&  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_init_return_wit_1 := 
forall (linklist_pre: Z) ,
  “ (linklist_pre <> 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> 0)
|--
  EX (linklist_pre_node_next: Z) ,
  “ (linklist_pre_node_next = 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> linklist_pre_node_next)
  **  (xizi_sll 0 nil )
.

Module Type VC_Correct.


Axiom proof_of_xizi_single_link_init_safety_wit_1 : xizi_single_link_init_safety_wit_1.
Axiom proof_of_xizi_single_link_init_return_wit_1 : xizi_single_link_init_return_wit_1.

End VC_Correct.
