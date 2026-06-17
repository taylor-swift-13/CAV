Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Psatz.
From SimpleC.SL Require Import SeparationLogic.
Import naive_C_Rules.
Require Import xizi_single_link_lib.
Local Open Scope Z_scope.
Local Open Scope sac.
Local Open Scope string.

Definition xizi_single_link_strategy301 :=
  forall (p : Z),
    TT &&
    emp **
    ((xizi_sll p (@nil Z)))
    |--
    (
    TT &&
    (“ (p = 0) ”) &&
    emp
    ) ** (
    TT &&
    emp -*
    TT &&
    emp
    ).

Definition xizi_single_link_strategy302 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z),
    TT &&
    (“ (p = 0) ”) &&
    emp -*
    TT &&
    emp **
    ((xizi_sll p (@nil Z)))
    ).

Definition xizi_single_link_strategy303 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((xizi_sll 0 l))
    ).

Definition xizi_single_link_strategy307 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((xizi_sllseg p p l))
    ).

Definition xizi_single_link_strategy310 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z),
    TT &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    emp **
    ((xizi_sll_to_target p p l))
    ).

Definition xizi_single_link_strategy312 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (l : (@list Z)) (p : Z) (q : Z),
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    (“ (l = (@nil Z)) ”) &&
    emp -*
    TT &&
    (“ (p = q) ” || “ (q = p) ”) &&
    emp **
    ((xizi_sllseg p q l))
    ).

Definition xizi_single_link_strategy305 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    emp **
    ((xizi_sll_head p l))
    |--
    EX (q : Z),
      (
      TT &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") q)) **
      ((xizi_sll q l))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition xizi_single_link_strategy306 :=
  TT &&
  emp
  |--
  (
  TT &&
  emp
  ) ** (
  ALL (p : Z) (q : Z) (l : (@list Z)),
    TT &&
    emp **
    ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") q)) **
    ((xizi_sll q l)) -*
    TT &&
    emp **
    ((xizi_sll_head p l))
    ).

Definition xizi_single_link_strategy304 :=
  forall (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((xizi_sll p l))
    |--
    EX (d : Z) (q : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") q)) **
      ((xizi_sll q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition xizi_single_link_strategy308 :=
  forall (q : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> q) ” || “ (q <> p) ”) &&
    emp **
    ((xizi_sllseg p q l))
    |--
    EX (d : Z) (r : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> q) ” || “ (q <> p) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") r)) **
      ((xizi_sllseg r q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition xizi_single_link_strategy309 :=
  forall (q : Z) (p : Z) (l : (@list Z)),
    TT &&
    (“ (p <> q) ” || “ (q <> p) ”) &&
    emp **
    ((xizi_sll_to_target p q l))
    |--
    EX (d : Z) (r : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> q) ” || “ (q <> p) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") r)) **
      ((xizi_sll_to_target r q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Definition xizi_single_link_strategy311 :=
  forall (p : Z) (q : Z) (l : (@list Z)),
    TT &&
    (“ (p <> 0) ” || “ (0 <> p) ”) &&
    emp **
    ((xizi_sll_not_target p q l))
    |--
    EX (d : Z) (r : Z) (l0 : (@list Z)),
      (
      TT &&
      (“ (p <> 0) ” || “ (0 <> p) ”) &&
      (“ (p <> q) ”) &&
      (“ (l = (@cons Z d l0)) ”) &&
      emp **
      ((poly_store FET_ptr &( ((p)) # "SingleLinklistNode" ->ₛ "node_next") r)) **
      ((xizi_sll_not_target r q l0))
      ) ** (
      TT &&
      emp -*
      TT &&
      emp
      ).

Module Type xizi_single_link_Strategy_Correct.

  Axiom xizi_single_link_strategy301_correctness : xizi_single_link_strategy301.
  Axiom xizi_single_link_strategy302_correctness : xizi_single_link_strategy302.
  Axiom xizi_single_link_strategy303_correctness : xizi_single_link_strategy303.
  Axiom xizi_single_link_strategy307_correctness : xizi_single_link_strategy307.
  Axiom xizi_single_link_strategy310_correctness : xizi_single_link_strategy310.
  Axiom xizi_single_link_strategy312_correctness : xizi_single_link_strategy312.
  Axiom xizi_single_link_strategy305_correctness : xizi_single_link_strategy305.
  Axiom xizi_single_link_strategy306_correctness : xizi_single_link_strategy306.
  Axiom xizi_single_link_strategy304_correctness : xizi_single_link_strategy304.
  Axiom xizi_single_link_strategy308_correctness : xizi_single_link_strategy308.
  Axiom xizi_single_link_strategy309_correctness : xizi_single_link_strategy309.
  Axiom xizi_single_link_strategy311_correctness : xizi_single_link_strategy311.

End xizi_single_link_Strategy_Correct.
