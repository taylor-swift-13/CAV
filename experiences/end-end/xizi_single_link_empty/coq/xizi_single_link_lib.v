Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import String.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Local Open Scope Z_scope.
Local Open Scope sets.
Import ListNotations.
Local Open Scope list.
Local Open Scope string_scope.

Import naive_C_Rules.
Local Open Scope sac.

Fixpoint xizi_sll (x: addr) (l: list Z): Assertion :=
  match l with
  | nil => “ x = NULL ” && emp
  | _ :: l0 =>
      “ x <> NULL ” &&
      EX y: addr,
        &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> y **
        xizi_sll y l0
  end.

Definition xizi_sll_head (head: addr) (l: list Z): Assertion :=
  EX first: addr,
    &(head # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> first **
    xizi_sll first l.

Lemma xizi_sll_zero: forall x l,
  x = NULL ->
  xizi_sll x l |-- “ l = nil ” && emp.
Proof.
  intros.
  destruct l.
  - entailer!.
  - simpl.
    Intros. Intros y.
    entailer!.
Qed.

Lemma xizi_sll_not_zero: forall x l,
  x <> NULL ->
  xizi_sll x l |--
    EX d y l0,
      “ l = d :: l0 ” &&
      &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> y **
      xizi_sll y l0.
Proof.
  intros.
  destruct l.
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros y.
    Exists z y l.
    entailer!.
Qed.
