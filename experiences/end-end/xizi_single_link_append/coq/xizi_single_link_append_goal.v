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
Require Import xizi_single_link_strategy_goal.
Require Import xizi_single_link_strategy_proof.

(*----- Function xizi_single_link_append -----*)

Definition xizi_single_link_append_safety_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (old_next: Z) (l: (@list Z)) (next: Z) (node: Z) (l1a: (@list Z)) (d: Z) (l1b: (@list Z)) (l0: (@list Z)) (d_2: Z) ,
  “ (l = (app (l1a) ((cons (d) (l1b))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l = (cons (d_2) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (next = 0) ”
  &&  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((( &( "linklist_node" ) )) # Ptr  |-> linklist_node_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> linklist_node_pre)
  **  (xizi_sllseg linklist_pre node l1a )
  **  (xizi_sll next l1b )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> old_next)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_append_entail_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (old_next: Z) (l: (@list Z)) ,
  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ”
  &&  (xizi_sll linklist_pre l )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> old_next)
|--
  EX (next: Z)  (l1a: (@list Z))  (d_2: Z)  (l1b: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l = (app (l1a) ((cons (d_2) (l1b))))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (l = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre linklist_pre l1a )
  **  (xizi_sll next l1b )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> old_next)
.

Definition xizi_single_link_append_entail_wit_2 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (old_next: Z) (l: (@list Z)) (next_2: Z) (node: Z) (l1a_2: (@list Z)) (d_3: Z) (l1b_2: (@list Z)) (l0_2: (@list Z)) (d_4: Z) ,
  “ (l = (app (l1a_2) ((cons (d_3) (l1b_2))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l = (cons (d_4) (l0_2))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (next_2 <> 0) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next_2)
  **  (xizi_sllseg linklist_pre node l1a_2 )
  **  (xizi_sll next_2 l1b_2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> old_next)
|--
  EX (next: Z)  (l1a: (@list Z))  (d_2: Z)  (l1b: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l = (app (l1a) ((cons (d_2) (l1b))))) ” 
  &&  “ (next_2 <> 0) ” 
  &&  “ (l = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ”
  &&  ((&((next_2)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre next_2 l1a )
  **  (xizi_sll next l1b )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> old_next)
.

Definition xizi_single_link_append_return_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (l: (@list Z)) (next: Z) (node: Z) (l1a: (@list Z)) (d: Z) (l1b: (@list Z)) (l0: (@list Z)) (d_2: Z) ,
  “ (l = (app (l1a) ((cons (d) (l1b))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l = (cons (d_2) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (next = 0) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> linklist_node_pre)
  **  (xizi_sllseg linklist_pre node l1a )
  **  (xizi_sll next l1b )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> 0)
|--
  (xizi_sll linklist_pre (app (l) ((cons (0) (nil)))) )
.

Module Type VC_Correct.

Include xizi_single_link_Strategy_Correct.

Axiom proof_of_xizi_single_link_append_safety_wit_1 : xizi_single_link_append_safety_wit_1.
Axiom proof_of_xizi_single_link_append_entail_wit_1 : xizi_single_link_append_entail_wit_1.
Axiom proof_of_xizi_single_link_append_entail_wit_2 : xizi_single_link_append_entail_wit_2.
Axiom proof_of_xizi_single_link_append_return_wit_1 : xizi_single_link_append_return_wit_1.

End VC_Correct.
