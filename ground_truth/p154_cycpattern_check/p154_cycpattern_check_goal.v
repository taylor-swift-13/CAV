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
Require Import string_bridge.
Require Import p154_cycpattern_check.
Local Open Scope sac.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_goal.
From SimpleC.EE.QCP_demos_LLM Require Import char_array_strategy_proof.

(*----- Function rotation_match_at -----*)

Definition rotation_match_at_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_match_at_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "ok" ) )) # Int  |-> 1)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rotation_match_at_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((shift_pre + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift_pre + j )) ”
.

Definition rotation_match_at_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "idx" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((shift_pre + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift_pre + j )) ”
.

Definition rotation_match_at_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) >= m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "idx" ) )) # Int  |-> (shift_pre + j ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (((shift_pre + j ) - m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((shift_pre + j ) - m_pre )) ”
.

Definition rotation_match_at_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) >= m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "idx" ) )) # Int  |-> (shift_pre + j ))
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (((shift_pre + j ) - m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((shift_pre + j ) - m_pre )) ”
.

Definition rotation_match_at_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((pos_pre + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos_pre + j )) ”
.

Definition rotation_match_at_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ok" ) )) # Int  |-> ok)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((pos_pre + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos_pre + j )) ”
.

Definition rotation_match_at_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ok" ) )) # Int  |-> ok)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rotation_match_at_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "idx" ) )) # Int  |-> idx)
  **  ((( &( "ok" ) )) # Int  |-> ok)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rotation_match_at_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) = (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rotation_match_at_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) = (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> ok)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rotation_match_at_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> 0)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rotation_match_at_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "ok" ) )) # Int  |-> 0)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition rotation_match_at_entail_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (1 = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre 0 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre 0 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_2_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) >= m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= ((shift_pre + j ) - m_pre )) ” 
  &&  “ (((shift_pre + j ) - m_pre ) < m_pre) ” 
  &&  “ (((shift_pre + j ) - m_pre ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= ((shift_pre + j ) - m_pre )) ” 
  &&  “ (((shift_pre + j ) - m_pre ) < m_pre) ” 
  &&  “ (((shift_pre + j ) - m_pre ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_2_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) >= m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= ((shift_pre + j ) - m_pre )) ” 
  &&  “ (((shift_pre + j ) - m_pre ) < m_pre) ” 
  &&  “ (((shift_pre + j ) - m_pre ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= ((shift_pre + j ) - m_pre )) ” 
  &&  “ (((shift_pre + j ) - m_pre ) < m_pre) ” 
  &&  “ (((shift_pre + j ) - m_pre ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_2_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (shift_pre + j )) ” 
  &&  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ ((shift_pre + j ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (shift_pre + j )) ” 
  &&  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ ((shift_pre + j ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_2_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (shift_pre + j )) ” 
  &&  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ ((shift_pre + j ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= (shift_pre + j )) ” 
  &&  “ ((shift_pre + j ) < m_pre) ” 
  &&  “ ((shift_pre + j ) = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_3_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_3_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) <> (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (0 = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_3_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) = (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_entail_wit_3_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ ((Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0) = (Znth idx (app (b_l) ((cons (0) (nil)))) 0)) ” 
  &&  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre (j + 1 ) ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ (j >= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_at_spec pos_pre shift_pre a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (ok = 0) ” 
  &&  “ ~((rotation_match_at_spec pos_pre shift_pre a_l b_l )) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_return_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (ok: Z) (j: Z) ,
  “ (j >= m_pre) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= m_pre) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_at_spec pos_pre shift_pre a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (ok = 0) ” 
  &&  “ ~((rotation_match_at_spec pos_pre shift_pre a_l b_l )) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_match_at_partial_solve_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (((a_pre + ((pos_pre + j ) * sizeof(CHAR) ) )) # Char  |-> (Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre (pos_pre + j ) 0 (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition rotation_match_at_partial_solve_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (((a_pre + ((pos_pre + j ) * sizeof(CHAR) ) )) # Char  |-> (Znth (pos_pre + j ) (app (a_l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i a_pre (pos_pre + j ) 0 (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition rotation_match_at_partial_solve_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 0) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (((b_pre + (idx * sizeof(CHAR) ) )) # Char  |-> (Znth idx (app (b_l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre idx 0 (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
.

Definition rotation_match_at_partial_solve_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (pos_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (j: Z) (idx: Z) (ok: Z) ,
  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= (n_pre + 1 )) ” 
  &&  “ (0 <= (m_pre + 1 )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos_pre) ” 
  &&  “ ((pos_pre + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j < m_pre) ” 
  &&  “ (0 <= idx) ” 
  &&  “ (idx < m_pre) ” 
  &&  “ (idx = (rot_index (shift_pre) (j) (m_pre))) ” 
  &&  “ (ok = 1) ” 
  &&  “ (rotation_match_progress pos_pre shift_pre j ok a_l b_l ) ”
  &&  (((b_pre + (idx * sizeof(CHAR) ) )) # Char  |-> (Znth idx (app (b_l) ((cons (0) (nil)))) 0))
  **  (CharArray.missing_i b_pre idx 0 (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
.

(*----- Function rotation_occurs_at_shift -----*)

Definition rotation_occurs_at_shift_safety_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  ((( &( "found" ) )) # Int  |->_)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rotation_occurs_at_shift_safety_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  ((( &( "pos" ) )) # Int  |->_)
  **  ((( &( "found" ) )) # Int  |-> 0)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition rotation_occurs_at_shift_safety_wit_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((n_pre - m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - m_pre )) ”
.

Definition rotation_occurs_at_shift_safety_wit_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ ((n_pre - m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre - m_pre )) ”
.

Definition rotation_occurs_at_shift_safety_wit_5 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_6 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_7 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_8 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_9 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition rotation_occurs_at_shift_safety_wit_10 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition rotation_occurs_at_shift_safety_wit_11 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition rotation_occurs_at_shift_safety_wit_12 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition rotation_occurs_at_shift_safety_wit_13 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_14 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition rotation_occurs_at_shift_safety_wit_15 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition rotation_occurs_at_shift_safety_wit_16 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition rotation_occurs_at_shift_safety_wit_17 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> 1)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition rotation_occurs_at_shift_safety_wit_18 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> 1)
|--
  “ ((pos + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (pos + 1 )) ”
.

Definition rotation_occurs_at_shift_entail_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) ,
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rotation_shift_search shift_pre 0 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (0 = 1) ” 
  &&  “ (rotation_shift_search shift_pre 0 0 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_entail_wit_2_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (1 = 0) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_entail_wit_2_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_match_at_spec pos shift_pre a_l b_l ) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (1 = 0) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_entail_wit_2_3 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_entail_wit_2_4 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_match_at_spec pos shift_pre a_l b_l )) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= (pos + 1 )) ” 
  &&  “ ((pos + 1 ) <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre (pos + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_return_wit_1 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos > (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_has_match shift_pre a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (found = 0) ” 
  &&  “ ~((rotation_shift_has_match shift_pre a_l b_l )) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_return_wit_2 := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos > (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_has_match shift_pre a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (found = 0) ” 
  &&  “ ~((rotation_shift_has_match shift_pre a_l b_l )) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition rotation_occurs_at_shift_partial_solve_wit_1_pure := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos) ” 
  &&  “ ((pos + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
.

Definition rotation_occurs_at_shift_partial_solve_wit_1_aux := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos) ” 
  &&  “ ((pos + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition rotation_occurs_at_shift_partial_solve_wit_1 := rotation_occurs_at_shift_partial_solve_wit_1_pure -> rotation_occurs_at_shift_partial_solve_wit_1_aux.

Definition rotation_occurs_at_shift_partial_solve_wit_2_pure := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "shift" ) )) # Int  |-> shift_pre)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "pos" ) )) # Int  |-> pos)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos) ” 
  &&  “ ((pos + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ”
.

Definition rotation_occurs_at_shift_partial_solve_wit_2_aux := 
forall (m_pre: Z) (n_pre: Z) (shift_pre: Z) (b_pre: Z) (a_pre: Z) (b_l: (@list Z)) (a_l: (@list Z)) (found: Z) (pos: Z) ,
  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n_pre)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m_pre)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= pos) ” 
  &&  “ ((pos + m_pre ) <= n_pre) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (pos <= (n_pre - m_pre )) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre < INT_MAX) ” 
  &&  “ (0 < m_pre) ” 
  &&  “ (m_pre <= n_pre) ” 
  &&  “ (m_pre < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n_pre) ” 
  &&  “ ((Zlength (b_l)) = m_pre) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n_pre)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m_pre)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift_pre) ” 
  &&  “ (shift_pre < m_pre) ” 
  &&  “ (0 <= pos) ” 
  &&  “ (pos <= ((n_pre - m_pre ) + 1 )) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_shift_search shift_pre pos found a_l b_l ) ”
  &&  (CharArray.full a_pre (n_pre + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m_pre + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition rotation_occurs_at_shift_partial_solve_wit_2 := rotation_occurs_at_shift_partial_solve_wit_2_pure -> rotation_occurs_at_shift_partial_solve_wit_2_aux.

(*----- Function p154_cycpattern_check -----*)

Definition p154_cycpattern_check_safety_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p154_cycpattern_check_safety_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 > retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p154_cycpattern_check_safety_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  ((( &( "found" ) )) # Int  |->_)
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p154_cycpattern_check_safety_wit_5 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  ((( &( "shift" ) )) # Int  |->_)
  **  ((( &( "found" ) )) # Int  |-> 0)
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p154_cycpattern_check_safety_wit_6 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_7 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_8 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_9 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_10 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition p154_cycpattern_check_safety_wit_11 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition p154_cycpattern_check_safety_wit_12 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition p154_cycpattern_check_safety_wit_13 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ False ”
.

Definition p154_cycpattern_check_safety_wit_14 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_15 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "ok" ) )) # Int  |-> retval)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p154_cycpattern_check_safety_wit_16 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ ((shift + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift + 1 )) ”
.

Definition p154_cycpattern_check_safety_wit_17 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
|--
  “ ((shift + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift + 1 )) ”
.

Definition p154_cycpattern_check_safety_wit_18 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> 1)
|--
  “ ((shift + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift + 1 )) ”
.

Definition p154_cycpattern_check_safety_wit_19 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> 1)
|--
  “ ((shift + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (shift + 1 )) ”
.

Definition p154_cycpattern_check_entail_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 <= retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((Znth (k_4) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m)) -> ((Znth (k_5) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  ((( &( "m0" ) )) # Int  |-> retval_2)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
|--
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m) ” 
  &&  “ (0 = 0) ” 
  &&  “ (rotation_any_search 0 0 a_l b_l ) ”
  &&  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= m) ” 
  &&  “ (0 = 1) ” 
  &&  “ (rotation_any_search 0 0 a_l b_l ) ”
  &&  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition p154_cycpattern_check_entail_wit_2_1 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (1 = 0) ” 
  &&  “ (rotation_any_search (shift + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rotation_any_search (shift + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition p154_cycpattern_check_entail_wit_2_2 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval = 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 1) ” 
  &&  “ (rotation_shift_has_match shift a_l b_l ) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (1 = 0) ” 
  &&  “ (rotation_any_search (shift + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (1 = 1) ” 
  &&  “ (rotation_any_search (shift + 1 ) 1 a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition p154_cycpattern_check_entail_wit_2_3 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search (shift + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search (shift + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition p154_cycpattern_check_entail_wit_2_4 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) (retval: Z) ,
  “ (retval <> 1) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (retval = 0) ” 
  &&  “ ~((rotation_shift_has_match shift a_l b_l )) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search (shift + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
  ||
  (“ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (shift + 1 )) ” 
  &&  “ ((shift + 1 ) <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search (shift + 1 ) found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) ))
.

Definition p154_cycpattern_check_return_wit_1 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift >= m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (problem_154_spec a_l b_l found ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_return_wit_2 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift >= m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (problem_154_spec a_l b_l found ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_return_wit_3 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 > retval) ” 
  &&  “ (retval_2 <> 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((Znth (k_4) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m)) -> ((Znth (k_5) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (problem_154_spec a_l b_l 0 ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_return_wit_4 := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) (retval_2: Z) ,
  “ (retval_2 = 0) ” 
  &&  “ (retval_2 = m) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < n)) -> ((Znth (k_4) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_5: Z) , (((0 <= k_5) /\ (k_5 < m)) -> ((Znth (k_5) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
|--
  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (problem_154_spec a_l b_l 1 ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_partial_solve_wit_1_pure := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  ((( &( "n0" ) )) # Int  |->_)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ”
.

Definition p154_cycpattern_check_partial_solve_wit_1_aux := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) ,
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < m)) -> ((Znth (k_3) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_partial_solve_wit_1 := p154_cycpattern_check_partial_solve_wit_1_pure -> p154_cycpattern_check_partial_solve_wit_1_aux.

Definition p154_cycpattern_check_partial_solve_wit_2_pure := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) ,
  “ (retval = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ”
  &&  ((( &( "m0" ) )) # Int  |->_)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  ((( &( "n0" ) )) # Int  |-> retval)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= m) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (m < INT_MAX) ”
.

Definition p154_cycpattern_check_partial_solve_wit_2_aux := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (retval: Z) ,
  “ (retval = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= m) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < m)) -> ((Znth (k) (b_l) (0)) <> 0)) ” 
  &&  “ (m < INT_MAX) ” 
  &&  “ (0 <= (n + 1 )) ” 
  &&  “ (retval = n) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < n)) -> ((Znth (k_2) (a_l) (0)) <> 0)) ” 
  &&  “ (0 <= (m + 1 )) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 <= m) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ”
  &&  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_partial_solve_wit_2 := p154_cycpattern_check_partial_solve_wit_2_pure -> p154_cycpattern_check_partial_solve_wit_2_aux.

Definition p154_cycpattern_check_partial_solve_wit_3_pure := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < m) ”
.

Definition p154_cycpattern_check_partial_solve_wit_3_aux := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < m) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 1) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_partial_solve_wit_3 := p154_cycpattern_check_partial_solve_wit_3_pure -> p154_cycpattern_check_partial_solve_wit_3_aux.

Definition p154_cycpattern_check_partial_solve_wit_4_pure := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  ((( &( "ok" ) )) # Int  |->_)
  **  ((( &( "a" ) )) # Ptr  |-> a_pre)
  **  ((( &( "b" ) )) # Ptr  |-> b_pre)
  **  ((( &( "n0" ) )) # Int  |-> n)
  **  ((( &( "m0" ) )) # Int  |-> m)
  **  ((( &( "shift" ) )) # Int  |-> shift)
  **  ((( &( "found" ) )) # Int  |-> found)
  **  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < m) ”
.

Definition p154_cycpattern_check_partial_solve_wit_4_aux := 
forall (b_pre: Z) (a_pre: Z) (m: Z) (b_l: (@list Z)) (n: Z) (a_l: (@list Z)) (found: Z) (shift: Z) ,
  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
|--
  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k: Z) , (((0 <= k) /\ (k < n)) -> ((Znth (k) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_2: Z) , (((0 <= k_2) /\ (k_2 < m)) -> ((Znth (k_2) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift < m) ” 
  &&  “ (shift < m) ” 
  &&  “ (0 <= n) ” 
  &&  “ (n < INT_MAX) ” 
  &&  “ (0 < m) ” 
  &&  “ (m <= n) ” 
  &&  “ (m < (INT_MAX ÷ 2 )) ” 
  &&  “ ((Zlength (a_l)) = n) ” 
  &&  “ ((Zlength (b_l)) = m) ” 
  &&  “ (problem_154_pre a_l b_l ) ” 
  &&  “ (ascii_range a_l ) ” 
  &&  “ (ascii_range b_l ) ” 
  &&  “ forall (k_3: Z) , (((0 <= k_3) /\ (k_3 < n)) -> ((Znth (k_3) (a_l) (0)) <> 0)) ” 
  &&  “ forall (k_4: Z) , (((0 <= k_4) /\ (k_4 < m)) -> ((Znth (k_4) (b_l) (0)) <> 0)) ” 
  &&  “ (0 <= shift) ” 
  &&  “ (shift <= m) ” 
  &&  “ (found = 0) ” 
  &&  “ (rotation_any_search shift found a_l b_l ) ”
  &&  (CharArray.full a_pre (n + 1 ) (app (a_l) ((cons (0) (nil)))) )
  **  (CharArray.full b_pre (m + 1 ) (app (b_l) ((cons (0) (nil)))) )
.

Definition p154_cycpattern_check_partial_solve_wit_4 := p154_cycpattern_check_partial_solve_wit_4_pure -> p154_cycpattern_check_partial_solve_wit_4_aux.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_rotation_match_at_safety_wit_1 : rotation_match_at_safety_wit_1.
Axiom proof_of_rotation_match_at_safety_wit_2 : rotation_match_at_safety_wit_2.
Axiom proof_of_rotation_match_at_safety_wit_3 : rotation_match_at_safety_wit_3.
Axiom proof_of_rotation_match_at_safety_wit_4 : rotation_match_at_safety_wit_4.
Axiom proof_of_rotation_match_at_safety_wit_5 : rotation_match_at_safety_wit_5.
Axiom proof_of_rotation_match_at_safety_wit_6 : rotation_match_at_safety_wit_6.
Axiom proof_of_rotation_match_at_safety_wit_7 : rotation_match_at_safety_wit_7.
Axiom proof_of_rotation_match_at_safety_wit_8 : rotation_match_at_safety_wit_8.
Axiom proof_of_rotation_match_at_safety_wit_9 : rotation_match_at_safety_wit_9.
Axiom proof_of_rotation_match_at_safety_wit_10 : rotation_match_at_safety_wit_10.
Axiom proof_of_rotation_match_at_safety_wit_11 : rotation_match_at_safety_wit_11.
Axiom proof_of_rotation_match_at_safety_wit_12 : rotation_match_at_safety_wit_12.
Axiom proof_of_rotation_match_at_safety_wit_13 : rotation_match_at_safety_wit_13.
Axiom proof_of_rotation_match_at_safety_wit_14 : rotation_match_at_safety_wit_14.
Axiom proof_of_rotation_match_at_entail_wit_1 : rotation_match_at_entail_wit_1.
Axiom proof_of_rotation_match_at_entail_wit_2_1 : rotation_match_at_entail_wit_2_1.
Axiom proof_of_rotation_match_at_entail_wit_2_2 : rotation_match_at_entail_wit_2_2.
Axiom proof_of_rotation_match_at_entail_wit_2_3 : rotation_match_at_entail_wit_2_3.
Axiom proof_of_rotation_match_at_entail_wit_2_4 : rotation_match_at_entail_wit_2_4.
Axiom proof_of_rotation_match_at_entail_wit_3_1 : rotation_match_at_entail_wit_3_1.
Axiom proof_of_rotation_match_at_entail_wit_3_2 : rotation_match_at_entail_wit_3_2.
Axiom proof_of_rotation_match_at_entail_wit_3_3 : rotation_match_at_entail_wit_3_3.
Axiom proof_of_rotation_match_at_entail_wit_3_4 : rotation_match_at_entail_wit_3_4.
Axiom proof_of_rotation_match_at_return_wit_1 : rotation_match_at_return_wit_1.
Axiom proof_of_rotation_match_at_return_wit_2 : rotation_match_at_return_wit_2.
Axiom proof_of_rotation_match_at_partial_solve_wit_1 : rotation_match_at_partial_solve_wit_1.
Axiom proof_of_rotation_match_at_partial_solve_wit_2 : rotation_match_at_partial_solve_wit_2.
Axiom proof_of_rotation_match_at_partial_solve_wit_3 : rotation_match_at_partial_solve_wit_3.
Axiom proof_of_rotation_match_at_partial_solve_wit_4 : rotation_match_at_partial_solve_wit_4.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_1 : rotation_occurs_at_shift_safety_wit_1.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_2 : rotation_occurs_at_shift_safety_wit_2.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_3 : rotation_occurs_at_shift_safety_wit_3.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_4 : rotation_occurs_at_shift_safety_wit_4.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_5 : rotation_occurs_at_shift_safety_wit_5.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_6 : rotation_occurs_at_shift_safety_wit_6.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_7 : rotation_occurs_at_shift_safety_wit_7.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_8 : rotation_occurs_at_shift_safety_wit_8.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_9 : rotation_occurs_at_shift_safety_wit_9.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_10 : rotation_occurs_at_shift_safety_wit_10.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_11 : rotation_occurs_at_shift_safety_wit_11.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_12 : rotation_occurs_at_shift_safety_wit_12.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_13 : rotation_occurs_at_shift_safety_wit_13.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_14 : rotation_occurs_at_shift_safety_wit_14.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_15 : rotation_occurs_at_shift_safety_wit_15.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_16 : rotation_occurs_at_shift_safety_wit_16.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_17 : rotation_occurs_at_shift_safety_wit_17.
Axiom proof_of_rotation_occurs_at_shift_safety_wit_18 : rotation_occurs_at_shift_safety_wit_18.
Axiom proof_of_rotation_occurs_at_shift_entail_wit_1 : rotation_occurs_at_shift_entail_wit_1.
Axiom proof_of_rotation_occurs_at_shift_entail_wit_2_1 : rotation_occurs_at_shift_entail_wit_2_1.
Axiom proof_of_rotation_occurs_at_shift_entail_wit_2_2 : rotation_occurs_at_shift_entail_wit_2_2.
Axiom proof_of_rotation_occurs_at_shift_entail_wit_2_3 : rotation_occurs_at_shift_entail_wit_2_3.
Axiom proof_of_rotation_occurs_at_shift_entail_wit_2_4 : rotation_occurs_at_shift_entail_wit_2_4.
Axiom proof_of_rotation_occurs_at_shift_return_wit_1 : rotation_occurs_at_shift_return_wit_1.
Axiom proof_of_rotation_occurs_at_shift_return_wit_2 : rotation_occurs_at_shift_return_wit_2.
Axiom proof_of_rotation_occurs_at_shift_partial_solve_wit_1_pure : rotation_occurs_at_shift_partial_solve_wit_1_pure.
Axiom proof_of_rotation_occurs_at_shift_partial_solve_wit_1 : rotation_occurs_at_shift_partial_solve_wit_1.
Axiom proof_of_rotation_occurs_at_shift_partial_solve_wit_2_pure : rotation_occurs_at_shift_partial_solve_wit_2_pure.
Axiom proof_of_rotation_occurs_at_shift_partial_solve_wit_2 : rotation_occurs_at_shift_partial_solve_wit_2.
Axiom proof_of_p154_cycpattern_check_safety_wit_1 : p154_cycpattern_check_safety_wit_1.
Axiom proof_of_p154_cycpattern_check_safety_wit_2 : p154_cycpattern_check_safety_wit_2.
Axiom proof_of_p154_cycpattern_check_safety_wit_3 : p154_cycpattern_check_safety_wit_3.
Axiom proof_of_p154_cycpattern_check_safety_wit_4 : p154_cycpattern_check_safety_wit_4.
Axiom proof_of_p154_cycpattern_check_safety_wit_5 : p154_cycpattern_check_safety_wit_5.
Axiom proof_of_p154_cycpattern_check_safety_wit_6 : p154_cycpattern_check_safety_wit_6.
Axiom proof_of_p154_cycpattern_check_safety_wit_7 : p154_cycpattern_check_safety_wit_7.
Axiom proof_of_p154_cycpattern_check_safety_wit_8 : p154_cycpattern_check_safety_wit_8.
Axiom proof_of_p154_cycpattern_check_safety_wit_9 : p154_cycpattern_check_safety_wit_9.
Axiom proof_of_p154_cycpattern_check_safety_wit_10 : p154_cycpattern_check_safety_wit_10.
Axiom proof_of_p154_cycpattern_check_safety_wit_11 : p154_cycpattern_check_safety_wit_11.
Axiom proof_of_p154_cycpattern_check_safety_wit_12 : p154_cycpattern_check_safety_wit_12.
Axiom proof_of_p154_cycpattern_check_safety_wit_13 : p154_cycpattern_check_safety_wit_13.
Axiom proof_of_p154_cycpattern_check_safety_wit_14 : p154_cycpattern_check_safety_wit_14.
Axiom proof_of_p154_cycpattern_check_safety_wit_15 : p154_cycpattern_check_safety_wit_15.
Axiom proof_of_p154_cycpattern_check_safety_wit_16 : p154_cycpattern_check_safety_wit_16.
Axiom proof_of_p154_cycpattern_check_safety_wit_17 : p154_cycpattern_check_safety_wit_17.
Axiom proof_of_p154_cycpattern_check_safety_wit_18 : p154_cycpattern_check_safety_wit_18.
Axiom proof_of_p154_cycpattern_check_safety_wit_19 : p154_cycpattern_check_safety_wit_19.
Axiom proof_of_p154_cycpattern_check_entail_wit_1 : p154_cycpattern_check_entail_wit_1.
Axiom proof_of_p154_cycpattern_check_entail_wit_2_1 : p154_cycpattern_check_entail_wit_2_1.
Axiom proof_of_p154_cycpattern_check_entail_wit_2_2 : p154_cycpattern_check_entail_wit_2_2.
Axiom proof_of_p154_cycpattern_check_entail_wit_2_3 : p154_cycpattern_check_entail_wit_2_3.
Axiom proof_of_p154_cycpattern_check_entail_wit_2_4 : p154_cycpattern_check_entail_wit_2_4.
Axiom proof_of_p154_cycpattern_check_return_wit_1 : p154_cycpattern_check_return_wit_1.
Axiom proof_of_p154_cycpattern_check_return_wit_2 : p154_cycpattern_check_return_wit_2.
Axiom proof_of_p154_cycpattern_check_return_wit_3 : p154_cycpattern_check_return_wit_3.
Axiom proof_of_p154_cycpattern_check_return_wit_4 : p154_cycpattern_check_return_wit_4.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_1_pure : p154_cycpattern_check_partial_solve_wit_1_pure.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_1 : p154_cycpattern_check_partial_solve_wit_1.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_2_pure : p154_cycpattern_check_partial_solve_wit_2_pure.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_2 : p154_cycpattern_check_partial_solve_wit_2.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_3_pure : p154_cycpattern_check_partial_solve_wit_3_pure.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_3 : p154_cycpattern_check_partial_solve_wit_3.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_4_pure : p154_cycpattern_check_partial_solve_wit_4_pure.
Axiom proof_of_p154_cycpattern_check_partial_solve_wit_4 : p154_cycpattern_check_partial_solve_wit_4.

End VC_Correct.
