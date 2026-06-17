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

(*----- Function xizi_single_link_tail -----*)

Definition xizi_single_link_tail_entail_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) ,
  “ (linklist_pre <> 0) ”
  &&  (xizi_sll linklist_pre l )
|--
  EX (next: Z)  (l1: (@list Z))  (d_2: Z)  (l2: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l = (app (l1) ((cons (d_2) (l2))))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (l = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre linklist_pre l1 )
  **  (xizi_sll next l2 )
.

Definition xizi_single_link_tail_entail_wit_2 := 
forall (linklist_pre: Z) (l: (@list Z)) (next_2: Z) (linklist: Z) (l1_2: (@list Z)) (d_3: Z) (l2_2: (@list Z)) (l0_2: (@list Z)) (d_4: Z) ,
  “ (l = (app (l1_2) ((cons (d_3) (l2_2))))) ” 
  &&  “ (linklist <> 0) ” 
  &&  “ (l = (cons (d_4) (l0_2))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (next_2 <> 0) ”
  &&  ((&((linklist)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next_2)
  **  (xizi_sllseg linklist_pre linklist l1_2 )
  **  (xizi_sll next_2 l2_2 )
|--
  EX (next: Z)  (l1: (@list Z))  (d_2: Z)  (l2: (@list Z))  (l0: (@list Z))  (d: Z) ,
  “ (l = (app (l1) ((cons (d_2) (l2))))) ” 
  &&  “ (next_2 <> 0) ” 
  &&  “ (l = (cons (d) (l0))) ” 
  &&  “ (linklist_pre <> 0) ”
  &&  ((&((next_2)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre next_2 l1 )
  **  (xizi_sll next l2 )
.

Definition xizi_single_link_tail_return_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (next: Z) (linklist: Z) (l1_2: (@list Z)) (d_2: Z) (l2: (@list Z)) (l0: (@list Z)) (d_3: Z) ,
  “ (l = (app (l1_2) ((cons (d_2) (l2))))) ” 
  &&  “ (linklist <> 0) ” 
  &&  “ (l = (cons (d_3) (l0))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ (next = 0) ”
  &&  ((&((linklist)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> next)
  **  (xizi_sllseg linklist_pre linklist l1_2 )
  **  (xizi_sll next l2 )
|--
  EX (retval_node_next: Z)  (l1: (@list Z))  (d: Z) ,
  “ (l = (app (l1) ((cons (d) (nil))))) ” 
  &&  “ (linklist <> 0) ” 
  &&  “ (retval_node_next = 0) ”
  &&  (xizi_sllseg linklist_pre linklist l1 )
  **  ((&((linklist)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> retval_node_next)
.

Module Type VC_Correct.

Include xizi_single_link_Strategy_Correct.

Axiom proof_of_xizi_single_link_tail_entail_wit_1 : xizi_single_link_tail_entail_wit_1.
Axiom proof_of_xizi_single_link_tail_entail_wit_2 : xizi_single_link_tail_entail_wit_2.
Axiom proof_of_xizi_single_link_tail_return_wit_1 : xizi_single_link_tail_return_wit_1.

End VC_Correct.
