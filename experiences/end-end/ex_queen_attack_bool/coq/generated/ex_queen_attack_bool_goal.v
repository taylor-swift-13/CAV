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

(*----- Function ex_queen_attack_bool -----*)

Definition ex_queen_attack_bool_safety_wit_1 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dr" ) )) # Int  |->_)
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ ((r1_pre - r2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (r1_pre - r2_pre )) ”
.

Definition ex_queen_attack_bool_safety_wit_2 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |->_)
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ ((c1_pre - c2_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (c1_pre - c2_pre )) ”
.

Definition ex_queen_attack_bool_safety_wit_3 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_queen_attack_bool_safety_wit_4 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ ((r1_pre - r2_pre ) <> (INT_MIN)) ”
.

Definition ex_queen_attack_bool_safety_wit_5 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_queen_attack_bool_safety_wit_6 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (-(r1_pre - r2_pre )))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition ex_queen_attack_bool_safety_wit_7 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (-(r1_pre - r2_pre )))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ ((c1_pre - c2_pre ) <> (INT_MIN)) ”
.

Definition ex_queen_attack_bool_safety_wit_8 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ ((c1_pre - c2_pre ) <> (INT_MIN)) ”
.

Definition ex_queen_attack_bool_safety_wit_9 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (r1_pre = r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (c1_pre - c2_pre ))
  **  ((( &( "dr" ) )) # Int  |-> (-(r1_pre - r2_pre )))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ False ”
.

Definition ex_queen_attack_bool_safety_wit_10 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (r1_pre = r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (-(c1_pre - c2_pre )))
  **  ((( &( "dr" ) )) # Int  |-> (-(r1_pre - r2_pre )))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ False ”
.

Definition ex_queen_attack_bool_safety_wit_11 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (c1_pre = c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (-(c1_pre - c2_pre )))
  **  ((( &( "dr" ) )) # Int  |-> (-(r1_pre - r2_pre )))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ False ”
.

Definition ex_queen_attack_bool_safety_wit_12 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (c1_pre = c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  ((( &( "dc" ) )) # Int  |-> (-(c1_pre - c2_pre )))
  **  ((( &( "dr" ) )) # Int  |-> (r1_pre - r2_pre ))
  **  ((( &( "c2" ) )) # Int  |-> c2_pre)
  **  ((( &( "r2" ) )) # Int  |-> r2_pre)
  **  ((( &( "c1" ) )) # Int  |-> c1_pre)
  **  ((( &( "r1" ) )) # Int  |-> r1_pre)
|--
  “ False ”
.

Definition ex_queen_attack_bool_return_wit_1 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((-(r1_pre - r2_pre )) <> (-(c1_pre - c2_pre ))) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((0 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((0 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_2 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((-(r1_pre - r2_pre )) = (-(c1_pre - c2_pre ))) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_3 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) <> (-(c1_pre - c2_pre ))) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((0 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((0 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_4 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) = (-(c1_pre - c2_pre ))) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_5 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre )) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((0 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((0 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_6 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((r1_pre - r2_pre ) = (c1_pre - c2_pre )) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_7 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((-(r1_pre - r2_pre )) <> (c1_pre - c2_pre )) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((0 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((0 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_8 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ ((-(r1_pre - r2_pre )) = (c1_pre - c2_pre )) ” 
  &&  “ (c1_pre <> c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_9 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (r1_pre = r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) < 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_10 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (r1_pre = r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_11 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (c1_pre = c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) < 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Definition ex_queen_attack_bool_return_wit_12 := 
forall (c2_pre: Z) (r2_pre: Z) (c1_pre: Z) (r1_pre: Z) ,
  “ (c1_pre = c2_pre) ” 
  &&  “ (r1_pre <> r2_pre) ” 
  &&  “ ((c1_pre - c2_pre ) >= 0) ” 
  &&  “ ((r1_pre - r2_pre ) >= 0) ” 
  &&  “ (0 <= r1_pre) ” 
  &&  “ (r1_pre <= INT_MAX) ” 
  &&  “ (0 <= c1_pre) ” 
  &&  “ (c1_pre <= INT_MAX) ” 
  &&  “ (0 <= r2_pre) ” 
  &&  “ (r2_pre <= INT_MAX) ” 
  &&  “ (0 <= c2_pre) ” 
  &&  “ (c2_pre <= INT_MAX) ”
  &&  emp
|--
  “ ((1 = 1) -> ((((r1_pre = r2_pre) \/ (c1_pre = c2_pre)) \/ ((r1_pre - r2_pre ) = (c1_pre - c2_pre ))) \/ ((r1_pre - r2_pre ) = (c2_pre - c1_pre )))) ” 
  &&  “ ((1 = 0) -> ((((r1_pre <> r2_pre) /\ (c1_pre <> c2_pre)) /\ ((r1_pre - r2_pre ) <> (c1_pre - c2_pre ))) /\ ((r1_pre - r2_pre ) <> (c2_pre - c1_pre )))) ”
  &&  emp
.

Module Type VC_Correct.


Axiom proof_of_ex_queen_attack_bool_safety_wit_1 : ex_queen_attack_bool_safety_wit_1.
Axiom proof_of_ex_queen_attack_bool_safety_wit_2 : ex_queen_attack_bool_safety_wit_2.
Axiom proof_of_ex_queen_attack_bool_safety_wit_3 : ex_queen_attack_bool_safety_wit_3.
Axiom proof_of_ex_queen_attack_bool_safety_wit_4 : ex_queen_attack_bool_safety_wit_4.
Axiom proof_of_ex_queen_attack_bool_safety_wit_5 : ex_queen_attack_bool_safety_wit_5.
Axiom proof_of_ex_queen_attack_bool_safety_wit_6 : ex_queen_attack_bool_safety_wit_6.
Axiom proof_of_ex_queen_attack_bool_safety_wit_7 : ex_queen_attack_bool_safety_wit_7.
Axiom proof_of_ex_queen_attack_bool_safety_wit_8 : ex_queen_attack_bool_safety_wit_8.
Axiom proof_of_ex_queen_attack_bool_safety_wit_9 : ex_queen_attack_bool_safety_wit_9.
Axiom proof_of_ex_queen_attack_bool_safety_wit_10 : ex_queen_attack_bool_safety_wit_10.
Axiom proof_of_ex_queen_attack_bool_safety_wit_11 : ex_queen_attack_bool_safety_wit_11.
Axiom proof_of_ex_queen_attack_bool_safety_wit_12 : ex_queen_attack_bool_safety_wit_12.
Axiom proof_of_ex_queen_attack_bool_return_wit_1 : ex_queen_attack_bool_return_wit_1.
Axiom proof_of_ex_queen_attack_bool_return_wit_2 : ex_queen_attack_bool_return_wit_2.
Axiom proof_of_ex_queen_attack_bool_return_wit_3 : ex_queen_attack_bool_return_wit_3.
Axiom proof_of_ex_queen_attack_bool_return_wit_4 : ex_queen_attack_bool_return_wit_4.
Axiom proof_of_ex_queen_attack_bool_return_wit_5 : ex_queen_attack_bool_return_wit_5.
Axiom proof_of_ex_queen_attack_bool_return_wit_6 : ex_queen_attack_bool_return_wit_6.
Axiom proof_of_ex_queen_attack_bool_return_wit_7 : ex_queen_attack_bool_return_wit_7.
Axiom proof_of_ex_queen_attack_bool_return_wit_8 : ex_queen_attack_bool_return_wit_8.
Axiom proof_of_ex_queen_attack_bool_return_wit_9 : ex_queen_attack_bool_return_wit_9.
Axiom proof_of_ex_queen_attack_bool_return_wit_10 : ex_queen_attack_bool_return_wit_10.
Axiom proof_of_ex_queen_attack_bool_return_wit_11 : ex_queen_attack_bool_return_wit_11.
Axiom proof_of_ex_queen_attack_bool_return_wit_12 : ex_queen_attack_bool_return_wit_12.

End VC_Correct.
