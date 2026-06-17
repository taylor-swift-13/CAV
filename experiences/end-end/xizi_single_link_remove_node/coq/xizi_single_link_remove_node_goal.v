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

(*----- Function xizi_single_link_remove_node -----*)

Definition xizi_single_link_remove_node_safety_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (l1: (@list Z)) (d: Z) (node: Z) (node_node_next: Z) ,
  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((( &( "linklist_node" ) )) # Ptr  |-> linklist_node_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_remove_node_safety_wit_2 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (l1: (@list Z)) (d: Z) (node: Z) (node_node_next: Z) ,
  “ (node_node_next = 0) ” 
  &&  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((( &( "linklist_node" ) )) # Ptr  |-> linklist_node_pre)
  **  ((( &( "node" ) )) # Ptr  |-> node)
  **  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  “ False ”
.

Definition xizi_single_link_remove_node_entail_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) ,
  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  (xizi_sll_to_target linklist_pre linklist_node_pre l_before )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  EX (next: Z)  (l1: (@list Z))  (d_2: Z)  (l2: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l_before = (app (l1) ((cons (d_2) (l2))))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (l_before = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre linklist_pre l1 )
  **  (xizi_sll_to_target next linklist_node_pre l2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
.

Definition xizi_single_link_remove_node_entail_wit_2 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (next_2: Z) (node: Z) (l1_2: (@list Z)) (d_3: Z) (l2_2: (@list Z)) (l0_2: (@list Z)) (d_4: Z) ,
  “ (next_2 <> linklist_node_pre) ” 
  &&  “ (next_2 <> 0) ” 
  &&  “ (l_before = (app (l1_2) ((cons (d_3) (l2_2))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l_before = (cons (d_4) (l0_2))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next_2)
  **  (xizi_sllseg linklist_pre node l1_2 )
  **  (xizi_sll_to_target next_2 linklist_node_pre l2_2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  EX (next: Z)  (l1: (@list Z))  (d_2: Z)  (l2: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l_before = (app (l1) ((cons (d_2) (l2))))) ” 
  &&  “ (next_2 <> 0) ” 
  &&  “ (l_before = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  ((&((next_2)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre next_2 l1 )
  **  (xizi_sll_to_target next linklist_node_pre l2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
.

Definition xizi_single_link_remove_node_entail_wit_3_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (next: Z) (node: Z) (l1_2: (@list Z)) (d_2: Z) (l2: (@list Z)) (l0: (@list Z)) (d_3: Z) ,
  “ (next = 0) ” 
  &&  “ (l_before = (app (l1_2) ((cons (d_2) (l2))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l_before = (cons (d_3) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre node l1_2 )
  **  (xizi_sll_to_target next linklist_node_pre l2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  EX (node_node_next: Z)  (l1: (@list Z))  (d: Z) ,
  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
.

Definition xizi_single_link_remove_node_entail_wit_3_2 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (next: Z) (node: Z) (l1_2: (@list Z)) (d_2: Z) (l2: (@list Z)) (l0: (@list Z)) (d_3: Z) ,
  “ (next = linklist_node_pre) ” 
  &&  “ (next <> 0) ” 
  &&  “ (l_before = (app (l1_2) ((cons (d_2) (l2))))) ” 
  &&  “ (node <> 0) ” 
  &&  “ (l_before = (cons (d_3) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (linklist_pre <> linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre node l1_2 )
  **  (xizi_sll_to_target next linklist_node_pre l2 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  EX (node_node_next: Z)  (l1: (@list Z))  (d: Z) ,
  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
.

Definition xizi_single_link_remove_node_return_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (l1: (@list Z)) (d: Z) (node: Z) (node_node_next: Z) ,
  “ (node_node_next <> 0) ” 
  &&  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((&((node_node_next)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  (xizi_sll target_next l_after )
|--
  “ (linklist_pre = linklist_pre) ”
  &&  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll linklist_pre (app (l_before) (l_after)) )
.

Definition xizi_single_link_remove_node_partial_solve_wit_1 := 
forall (linklist_node_pre: Z) (linklist_pre: Z) (target_next: Z) (l_after: (@list Z)) (l_before: (@list Z)) (l1: (@list Z)) (d: Z) (node: Z) (node_node_next: Z) ,
  “ (node_node_next <> 0) ” 
  &&  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  ((&((linklist_node_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  (xizi_sll target_next l_after )
|--
  “ (node_node_next <> 0) ” 
  &&  “ (l_before = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist_node_pre <> 0) ” 
  &&  “ (node <> 0) ” 
  &&  “ (node_node_next = linklist_node_pre) ”
  &&  ((&((node_node_next)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> target_next)
  **  ((&((node)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> node_node_next)
  **  (xizi_sllseg linklist_pre node l1 )
  **  (xizi_sll target_next l_after )
.

Module Type VC_Correct.

Include xizi_single_link_Strategy_Correct.

Axiom proof_of_xizi_single_link_remove_node_safety_wit_1 : xizi_single_link_remove_node_safety_wit_1.
Axiom proof_of_xizi_single_link_remove_node_safety_wit_2 : xizi_single_link_remove_node_safety_wit_2.
Axiom proof_of_xizi_single_link_remove_node_entail_wit_1 : xizi_single_link_remove_node_entail_wit_1.
Axiom proof_of_xizi_single_link_remove_node_entail_wit_2 : xizi_single_link_remove_node_entail_wit_2.
Axiom proof_of_xizi_single_link_remove_node_entail_wit_3_1 : xizi_single_link_remove_node_entail_wit_3_1.
Axiom proof_of_xizi_single_link_remove_node_entail_wit_3_2 : xizi_single_link_remove_node_entail_wit_3_2.
Axiom proof_of_xizi_single_link_remove_node_return_wit_1 : xizi_single_link_remove_node_return_wit_1.
Axiom proof_of_xizi_single_link_remove_node_partial_solve_wit_1 : xizi_single_link_remove_node_partial_solve_wit_1.

End VC_Correct.
