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

(*----- Function xizi_single_link_empty -----*)

Definition xizi_single_link_empty_safety_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) ,
  “ (linklist_pre <> 0) ”
  &&  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_empty_return_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) ,
  “ (first = 0) ” 
  &&  “ (linklist_pre <> 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
|--
  “ ((first = 0) -> (1 = 1)) ” 
  &&  “ ((first <> 0) -> (1 = 0)) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
.

Definition xizi_single_link_empty_return_wit_2 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) ,
  “ (first <> 0) ” 
  &&  “ (linklist_pre <> 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
|--
  “ ((first = 0) -> (0 = 1)) ” 
  &&  “ ((first <> 0) -> (0 = 0)) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
.

Module Type VC_Correct.


Axiom proof_of_xizi_single_link_empty_safety_wit_1 : xizi_single_link_empty_safety_wit_1.
Axiom proof_of_xizi_single_link_empty_return_wit_1 : xizi_single_link_empty_return_wit_1.
Axiom proof_of_xizi_single_link_empty_return_wit_2 : xizi_single_link_empty_return_wit_2.

End VC_Correct.
