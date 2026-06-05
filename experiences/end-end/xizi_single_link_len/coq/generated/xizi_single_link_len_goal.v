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
Require Import xizi_single_link_len.
Local Open Scope sac.
Require Import int_array_strategy_goal.
Require Import int_array_strategy_proof.
Require Import uint_array_strategy_goal.
Require Import uint_array_strategy_proof.
Require Import undef_uint_array_strategy_goal.
Require Import undef_uint_array_strategy_proof.
Require Import array_shape_strategy_goal.
Require Import array_shape_strategy_proof.

(*----- Function xizi_single_link_len -----*)

Definition xizi_single_link_len_safety_wit_1 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  ((( &( "length" ) )) # Int  |->_)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "head" ) )) # Int  |-> head_pre)
  **  (IntArray.full next_pre n l )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition xizi_single_link_len_safety_wit_2 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  ((( &( "length" ) )) # Int  |-> length)
  **  ((( &( "head" ) )) # Int  |-> head_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "node" ) )) # Int  |-> node)
  **  (IntArray.full next_pre n l )
|--
  “ (1 <> (INT_MIN)) ”
.

Definition xizi_single_link_len_safety_wit_3 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  ((( &( "length" ) )) # Int  |-> length)
  **  ((( &( "head" ) )) # Int  |-> head_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "node" ) )) # Int  |-> node)
  **  (IntArray.full next_pre n l )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition xizi_single_link_len_safety_wit_4 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (node <> (-1)) ” 
  &&  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
  **  ((( &( "length" ) )) # Int  |-> length)
  **  ((( &( "head" ) )) # Int  |-> head_pre)
  **  ((( &( "next" ) )) # Ptr  |-> next_pre)
  **  ((( &( "node" ) )) # Int  |-> (Znth node l 0))
|--
  “ ((length + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (length + 1 )) ”
.

Definition xizi_single_link_len_entail_wit_1 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= n) ” 
  &&  “ (((Znth head_pre l 0) = (-1)) -> (0 = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (((Znth head_pre l 0) <> (-1)) -> ((0 <= (Znth head_pre l 0)) /\ ((Znth head_pre l 0) < n))) ” 
  &&  “ (((Znth head_pre l 0) <> (-1)) -> (xizi_single_link_wf (Znth head_pre l 0) l )) ” 
  &&  “ (((Znth head_pre l 0) <> (-1)) -> (((0 + 1 ) + (xizi_single_link_len_spec ((Znth head_pre l 0)) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
.

Definition xizi_single_link_len_entail_wit_2 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (node <> (-1)) ” 
  &&  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
|--
  “ (0 <= (length + 1 )) ” 
  &&  “ ((length + 1 ) <= n) ” 
  &&  “ (((Znth node l 0) = (-1)) -> ((length + 1 ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (((Znth node l 0) <> (-1)) -> ((0 <= (Znth node l 0)) /\ ((Znth node l 0) < n))) ” 
  &&  “ (((Znth node l 0) <> (-1)) -> (xizi_single_link_wf (Znth node l 0) l )) ” 
  &&  “ (((Znth node l 0) <> (-1)) -> ((((length + 1 ) + 1 ) + (xizi_single_link_len_spec ((Znth node l 0)) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
.

Definition xizi_single_link_len_return_wit_1 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (node = (-1)) ” 
  &&  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
|--
  “ (length = (xizi_single_link_len_spec (head_pre) (l))) ”
  &&  (IntArray.full next_pre n l )
.

Definition xizi_single_link_len_partial_solve_wit_1 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) ,
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
|--
  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (((next_pre + (head_pre * sizeof(INT) ) )) # Int  |-> (Znth head_pre l 0))
  **  (IntArray.missing_i next_pre head_pre 0 n l )
.

Definition xizi_single_link_len_partial_solve_wit_2 := 
forall (next_pre: Z) (head_pre: Z) (l: (@list Z)) (n: Z) (node: Z) (length: Z) ,
  “ (node <> (-1)) ” 
  &&  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (IntArray.full next_pre n l )
|--
  “ (node <> (-1)) ” 
  &&  “ (0 <= length) ” 
  &&  “ (length <= n) ” 
  &&  “ ((node = (-1)) -> (length = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ ((node <> (-1)) -> ((0 <= node) /\ (node < n))) ” 
  &&  “ ((node <> (-1)) -> (xizi_single_link_wf node l )) ” 
  &&  “ ((node <> (-1)) -> (((length + 1 ) + (xizi_single_link_len_spec (node) (l)) ) = (xizi_single_link_len_spec (head_pre) (l)))) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n <= INT_MAX) ” 
  &&  “ ((Zlength (l)) = n) ” 
  &&  “ (0 <= head_pre) ” 
  &&  “ (head_pre < n) ” 
  &&  “ (xizi_single_link_wf head_pre l ) ”
  &&  (((next_pre + (node * sizeof(INT) ) )) # Int  |-> (Znth node l 0))
  **  (IntArray.missing_i next_pre node 0 n l )
.

Module Type VC_Correct.

Include int_array_Strategy_Correct.
Include uint_array_Strategy_Correct.
Include undef_uint_array_Strategy_Correct.
Include array_shape_Strategy_Correct.

Axiom proof_of_xizi_single_link_len_safety_wit_1 : xizi_single_link_len_safety_wit_1.
Axiom proof_of_xizi_single_link_len_safety_wit_2 : xizi_single_link_len_safety_wit_2.
Axiom proof_of_xizi_single_link_len_safety_wit_3 : xizi_single_link_len_safety_wit_3.
Axiom proof_of_xizi_single_link_len_safety_wit_4 : xizi_single_link_len_safety_wit_4.
Axiom proof_of_xizi_single_link_len_entail_wit_1 : xizi_single_link_len_entail_wit_1.
Axiom proof_of_xizi_single_link_len_entail_wit_2 : xizi_single_link_len_entail_wit_2.
Axiom proof_of_xizi_single_link_len_return_wit_1 : xizi_single_link_len_return_wit_1.
Axiom proof_of_xizi_single_link_len_partial_solve_wit_1 : xizi_single_link_len_partial_solve_wit_1.
Axiom proof_of_xizi_single_link_len_partial_solve_wit_2 : xizi_single_link_len_partial_solve_wit_2.

End VC_Correct.
