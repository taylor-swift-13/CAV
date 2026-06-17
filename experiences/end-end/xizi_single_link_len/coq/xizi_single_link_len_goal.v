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

(*----- Function xizi_single_link_len -----*)

Definition xizi_single_link_len_safety_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) ,
  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((( &( "length" ) )) # UInt  |->_)
  **  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_len_safety_wit_2 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) (tmp_list: Z) (length: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (length = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((( &( "length" ) )) # UInt  |-> length)
  **  ((( &( "linklist" ) )) # Ptr  |-> linklist_pre)
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  ((( &( "tmp_list" ) )) # Ptr  |-> tmp_list)
  **  (xizi_sllseg first tmp_list l1 )
  **  (xizi_sll tmp_list l2 )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_len_entail_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) ,
  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ (0 = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first first l1 )
  **  (xizi_sll first l2 )
.

Definition xizi_single_link_len_entail_wit_2 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) (tmp_list: Z) (length: Z) (l1_2: (@list Z)) (l2_2: (@list Z)) (d: Z) (q: Z) (l0: (@list Z)) ,
  “ (l2_2 = (cons (d) (l0))) ” 
  &&  “ (tmp_list <> 0) ” 
  &&  “ (l = (app (l1_2) (l2_2))) ” 
  &&  “ (length = (Zlength (l1_2))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((tmp_list)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> q)
  **  (xizi_sll q l0 )
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first tmp_list l1_2 )
|--
  EX (l1: (@list Z))  (l2: (@list Z)) ,
  “ (l = (app (l1) (l2))) ” 
  &&  “ ((unsigned_last_nbits ((length + 1 )) (32)) = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first q l1 )
  **  (xizi_sll q l2 )
.

Definition xizi_single_link_len_return_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) (tmp_list: Z) (length: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  “ (tmp_list = 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (length = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first tmp_list l1 )
  **  (xizi_sll tmp_list l2 )
|--
  “ (length = (Zlength (l))) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sll first l )
.

Definition xizi_single_link_len_partial_solve_wit_1 := 
forall (linklist_pre: Z) (l: (@list Z)) (first: Z) (tmp_list: Z) (length: Z) (l1: (@list Z)) (l2: (@list Z)) ,
  “ (tmp_list <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (length = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first tmp_list l1 )
  **  (xizi_sll tmp_list l2 )
|--
  EX (l0: (@list Z))  (q: Z)  (d: Z) ,
  “ (l2 = (cons (d) (l0))) ” 
  &&  “ (tmp_list <> 0) ” 
  &&  “ (l = (app (l1) (l2))) ” 
  &&  “ (length = (Zlength (l1))) ” 
  &&  “ (linklist_pre <> 0) ” 
  &&  “ ((Zlength (l)) <= UINT_MAX) ”
  &&  ((&((tmp_list)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> q)
  **  (xizi_sll q l0 )
  **  ((&((linklist_pre)  # "SingleLinklistNode" ->ₛ "node_next")) # Ptr  |-> first)
  **  (xizi_sllseg first tmp_list l1 )
.

Module Type VC_Correct.

Include xizi_single_link_Strategy_Correct.

Axiom proof_of_xizi_single_link_len_safety_wit_1 : xizi_single_link_len_safety_wit_1.
Axiom proof_of_xizi_single_link_len_safety_wit_2 : xizi_single_link_len_safety_wit_2.
Axiom proof_of_xizi_single_link_len_entail_wit_1 : xizi_single_link_len_entail_wit_1.
Axiom proof_of_xizi_single_link_len_entail_wit_2 : xizi_single_link_len_entail_wit_2.
Axiom proof_of_xizi_single_link_len_return_wit_1 : xizi_single_link_len_return_wit_1.
Axiom proof_of_xizi_single_link_len_partial_solve_wit_1 : xizi_single_link_len_partial_solve_wit_1.

End VC_Correct.
