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

Fixpoint xizi_sllseg (x y: addr) (l: list Z): Assertion :=
  match l with
  | nil => “ x = y ” && emp
  | _ :: l0 =>
      “ x <> NULL ” &&
      EX z: addr,
        &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
        xizi_sllseg z y l0
  end.

Fixpoint xizi_sll_to_target (x y: addr) (l: list Z): Assertion :=
  match l with
  | nil => “ x = y ” && emp
  | _ :: l0 =>
      “ x <> NULL ” &&
      “ x <> y ” &&
      EX z: addr,
        &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
        xizi_sll_to_target z y l0
  end.

Fixpoint xizi_sll_not_target (x y: addr) (l: list Z): Assertion :=
  match l with
  | nil => “ x = NULL ” && emp
  | _ :: l0 =>
      “ x <> NULL ” &&
      “ x <> y ” &&
      EX z: addr,
        &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
        xizi_sll_not_target z y l0
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
  destruct l as [| d l0].
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros y.
    Exists d y l0.
    entailer!.
Qed.

Lemma xizi_sllseg_len1: forall x a y,
  x <> NULL ->
  &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> y |--
  xizi_sllseg x y [a].
Proof.
  intros.
  simpl xizi_sllseg.
  Exists y.
  entailer!.
Qed.

Lemma xizi_sllseg_not_same: forall x y l,
  x <> y ->
  xizi_sllseg x y l |--
    EX d z l0,
      “ l = d :: l0 ” &&
      &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
      xizi_sllseg z y l0.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros z.
    Exists d z l0.
    entailer!.
Qed.

Lemma xizi_sll_to_target_not_same: forall x y l,
  x <> y ->
  xizi_sll_to_target x y l |--
    EX d z l0,
      “ l = d :: l0 ” &&
      &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
      xizi_sll_to_target z y l0.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros z.
    Exists d z l0.
    entailer!.
Qed.

Lemma xizi_sll_to_target_same: forall x l,
  xizi_sll_to_target x x l |--
  “ l = nil ” && emp.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    entailer!.
  - simpl.
    Intros. Intros z0.
    entailer!.
Qed.

Lemma xizi_sll_to_target_zero_nonzero: forall y l,
  y <> NULL ->
  xizi_sll_to_target NULL y l |-- “ False ”.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    subst y.
    tauto.
  - simpl.
    Intros. Intros z0.
    entailer!.
Qed.

Lemma xizi_sll_not_target_not_zero: forall x y l,
  x <> NULL ->
  xizi_sll_not_target x y l |--
    EX d z l0,
      “ l = d :: l0 ” &&
      “ x <> y ” &&
      &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> z **
      xizi_sll_not_target z y l0.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros z.
    Exists d z l0.
    entailer!.
Qed.

Lemma xizi_sll_not_target_zero: forall y l,
  xizi_sll_not_target NULL y l |-- “ l = nil ” && emp.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    entailer!.
  - simpl.
    Intros. Intros z0.
    entailer!.
Qed.

Lemma xizi_sll_not_target_same_nonzero: forall x l,
  x <> NULL ->
  xizi_sll_not_target x x l |-- “ False ”.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    tauto.
  - simpl.
    Intros. Intros z0.
    entailer!.
Qed.

Lemma xizi_sll_not_target_sll: forall x y l,
  xizi_sll_not_target x y l |-- xizi_sll x l.
Proof.
  intros.
  revert x; induction l as [| d l0 IH]; intros.
  - simpl.
    Intros.
    entailer!.
  - simpl.
    Intros. Intros z.
    Exists z.
    sep_apply IH.
    entailer!.
Qed.

Lemma xizi_sllseg_sllseg: forall x y z l1 l2,
  xizi_sllseg x y l1 ** xizi_sllseg y z l2 |--
  xizi_sllseg x z (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl xizi_sllseg; intros.
  - Intros.
    subst y.
    entailer!.
  - Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma xizi_sllseg_sll: forall x y l1 l2,
  xizi_sllseg x y l1 ** xizi_sll y l2 |--
  xizi_sll x (l1 ++ l2).
Proof.
  intros.
  revert x; induction l1; simpl xizi_sllseg; simpl xizi_sll; intros.
  - Intros.
    subst y.
    entailer!.
  - Intros. Intros z0.
    Exists z0.
    sep_apply IHl1.
    entailer!.
Qed.

Lemma xizi_sllseg_0_sll: forall x l,
  xizi_sllseg x 0 l |--
  xizi_sll x l.
Proof.
  intros.
  revert x; induction l; simpl xizi_sllseg; simpl xizi_sll; intros.
  - Intros.
    subst x.
    entailer!.
  - Intros. Intros z0.
    Exists z0.
    sep_apply IHl.
        entailer!.
Qed.

Lemma xizi_sllseg_zero_nonzero: forall y l,
  y <> NULL ->
  xizi_sllseg NULL y l |-- “ False ”.
Proof.
  intros.
  destruct l as [| d l0].
  - simpl.
    Intros.
    subst y.
    tauto.
  - simpl.
    Intros. Intros z0.
    entailer!.
Qed.

Lemma xizi_sll_cons: forall x d y l,
  x <> NULL ->
  &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> y **
  xizi_sll y l |--
  xizi_sll x (d :: l).
Proof.
  intros.
  simpl xizi_sll.
  Exists y.
  entailer!.
Qed.

Lemma xizi_sll_len1: forall x d y,
  x <> NULL ->
  y = NULL ->
  &(x # "SingleLinklistNode" ->ₛ "node_next") # Ptr |-> y |--
  xizi_sll x [d].
Proof.
  intros.
  subst y.
  simpl xizi_sll.
  Exists NULL.
  entailer!.
Qed.
