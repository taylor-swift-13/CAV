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
From SimpleC.EE.CAV.verify_20260603_193124v_xizi_single_link_len Require Import xizi_single_link_len_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import xizi_single_link_len.
Local Open Scope sac.

Lemma xizi_next_at_eq_Znth :
  forall idx l,
    0 <= idx < Zlength l ->
    xizi_next_at idx l = Znth idx l 0.
Proof.
  intros idx l Hr.
  unfold xizi_next_at.
  rewrite (Znth_indep l idx 0 (-1)) by exact Hr.
  unfold Znth.
  reflexivity.
Qed.

Lemma xizi_single_link_spec_nonneg :
  forall fuel node nexts,
    0 <= xizi_single_link_len_nat fuel node nexts.
Proof.
  induction fuel as [|fuel IH]; intros node nexts; simpl.
  - lia.
  - destruct (Z.eq_dec node (-1)).
    + lia.
    + specialize (IH (xizi_next_at node nexts) nexts).
      change (0 <= 1 + xizi_single_link_len_nat fuel (xizi_next_at node nexts) nexts).
      lia.
Qed.

Lemma xizi_single_link_len_nat_fuel_bound :
  forall fuel node nexts,
    xizi_single_link_len_nat fuel node nexts <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros node nexts; simpl.
  - lia.
  - destruct (Z.eq_dec node (-1)).
    + lia.
    + specialize (IH (xizi_next_at node nexts) nexts).
      change (1 + xizi_single_link_len_nat fuel (xizi_next_at node nexts) nexts <= Z.of_nat (S fuel)).
      replace (Z.of_nat (S fuel)) with (1 + Z.of_nat fuel) by lia.
      lia.
Qed.

Lemma xizi_single_link_len_spec_bound_any :
  forall node l,
    xizi_single_link_len_spec node l <= Zlength l.
Proof.
  intros node l.
  unfold xizi_single_link_len_spec.
  rewrite Nat2Z.id.
  apply Z.le_trans with (m := Z.of_nat (length l)).
  - apply xizi_single_link_len_nat_fuel_bound.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma xizi_single_link_len_nat_neg1 :
  forall fuel nexts,
    xizi_single_link_len_nat fuel (-1) nexts = 0.
Proof.
  induction fuel as [|fuel IH]; intros nexts; simpl.
  - reflexivity.
  - destruct (Z.eq_dec (-1) (-1)) as [_|Hcontra].
    + reflexivity.
    + contradiction Hcontra; reflexivity.
Qed.

Lemma xizi_single_link_len_nat_unfold :
  forall fuel node nexts,
    node <> -1 ->
    xizi_single_link_len_nat (S fuel) node nexts =
    1 + xizi_single_link_len_nat fuel (xizi_next_at node nexts) nexts.
Proof.
  intros fuel node nexts Hneq.
  simpl.
  destruct (Z.eq_dec node (-1)) as [Heq|_].
  - contradiction.
  - reflexivity.
Qed.

Lemma xizi_single_link_valid_unfold :
  forall fuel seen node nexts,
    node <> -1 ->
    xizi_single_link_valid_nat (S fuel) seen node nexts ->
    0 <= node < Zlength nexts /\
    xizi_member node seen = false /\
    xizi_single_link_valid_nat fuel (node :: seen) (xizi_next_at node nexts) nexts.
Proof.
  intros fuel seen node nexts Hneq Hvalid.
  simpl in Hvalid.
  destruct (Z.eq_dec node (-1)) as [Heq|Hne].
  - contradiction.
  - destruct Hvalid as [Hrange [Hfresh Htail]].
    rewrite Zlength_correct.
    tauto.
Qed.

Lemma xizi_single_link_valid_weaken_seen :
  forall fuel seen_big seen_small node nexts,
    (forall x,
      xizi_member x seen_big = false ->
      xizi_member x seen_small = false) ->
    xizi_single_link_valid_nat fuel seen_big node nexts ->
    xizi_single_link_valid_nat fuel seen_small node nexts.
Proof.
  induction fuel as [|fuel IH]; intros seen_big seen_small node nexts Hsubset Hvalid.
  - exact Hvalid.
  - simpl in *.
    destruct (Z.eq_dec node (-1)) as [Heq|Hneq].
    + exact I.
    + destruct Hvalid as [Hrange [Hfresh Htail]].
      split.
      * exact Hrange.
      * split.
        -- apply Hsubset. exact Hfresh.
        -- apply IH with (seen_big := node :: seen_big).
           ++ intros x Hmem.
              simpl in Hmem.
              destruct (Z.eq_dec x node) as [Hx|Hx].
              ** subst x.
                 destruct (Z.eq_dec node node) as [_|Hcontra].
                 --- discriminate.
                 --- contradiction Hcontra; reflexivity.
              ** simpl.
                 destruct (Z.eq_dec x node) as [Hcontra|_].
                 --- contradiction.
                 --- apply Hsubset. exact Hmem.
           ++ exact Htail.
Qed.

Lemma xizi_single_link_valid_increase_fuel_once :
  forall fuel seen node nexts,
    xizi_single_link_valid_nat fuel seen node nexts ->
    xizi_single_link_valid_nat (S fuel) seen node nexts.
Proof.
  induction fuel as [|fuel IH]; intros seen node nexts Hvalid.
  - simpl in Hvalid.
    subst node.
    simpl.
    destruct (Z.eq_dec (-1) (-1)) as [_|Hcontra].
    + exact I.
    + contradiction Hcontra; reflexivity.
  - simpl in Hvalid.
    simpl.
    destruct (Z.eq_dec node (-1)) as [Heq|Hneq].
    + exact I.
    + destruct Hvalid as [Hrange [Hfresh Htail]].
      split.
      * exact Hrange.
      * split.
        -- exact Hfresh.
        -- change (xizi_single_link_valid_nat (S fuel) (node :: seen)
             (xizi_next_at node nexts) nexts).
           apply IH. exact Htail.
Qed.

Lemma xizi_single_link_valid_increase_fuel :
  forall fuel extra seen node nexts,
    xizi_single_link_valid_nat fuel seen node nexts ->
    xizi_single_link_valid_nat (fuel + extra) seen node nexts.
Proof.
  induction extra as [|extra IH]; intros seen node nexts Hvalid.
  - rewrite Nat.add_0_r. exact Hvalid.
  - rewrite Nat.add_succ_r.
    apply xizi_single_link_valid_increase_fuel_once.
    apply IH.
    exact Hvalid.
Qed.

Lemma xizi_single_link_len_nat_stable :
  forall fuel extra seen node nexts,
    xizi_single_link_valid_nat fuel seen node nexts ->
    xizi_single_link_len_nat (fuel + extra) node nexts =
    xizi_single_link_len_nat fuel node nexts.
Proof.
  induction fuel as [|fuel IH]; intros extra seen node nexts Hvalid.
  - simpl in Hvalid.
    subst node.
    rewrite xizi_single_link_len_nat_neg1.
    symmetry.
    apply xizi_single_link_len_nat_neg1.
  - simpl in *.
    destruct (Z.eq_dec node (-1)) as [Heq|Hneq].
    + subst node.
      repeat rewrite xizi_single_link_len_nat_neg1.
      reflexivity.
    + destruct Hvalid as [_ [_ Htail]].
      simpl.
      destruct extra as [|extra].
      * rewrite Nat.add_0_r. reflexivity.
      * simpl.
        rewrite IH with (seen := node :: seen) (extra := S extra) by exact Htail.
        reflexivity.
Qed.

Lemma xizi_single_link_len_nat_valid_step :
  forall fuel seen node nexts,
    node <> -1 ->
    xizi_single_link_valid_nat (S fuel) seen node nexts ->
    1 + xizi_single_link_len_nat (S fuel) (xizi_next_at node nexts) nexts =
    xizi_single_link_len_nat (S fuel) node nexts.
Proof.
  intros fuel seen node nexts Hneq Hvalid.
  change (1 + xizi_single_link_len_nat (S fuel) (xizi_next_at node nexts) nexts =
    (if Z.eq_dec node (-1) then 0
     else 1 + xizi_single_link_len_nat fuel (xizi_next_at node nexts) nexts)).
  destruct (Z.eq_dec node (-1)) as [Heq|_].
  - contradiction.
  - f_equal.
    simpl in Hvalid.
    destruct (Z.eq_dec node (-1)) as [Heq|_].
    + contradiction.
    + destruct Hvalid as [_ [_ Htail]].
      replace (S fuel) with (fuel + 1)%nat by lia.
      apply xizi_single_link_len_nat_stable with (seen := node :: seen).
      exact Htail.
Qed.

Lemma xizi_single_link_wf_step :
  forall node l,
    xizi_single_link_wf node l ->
    let nxt := Znth node l 0 in
    (nxt = -1 -> xizi_single_link_len_spec node l = 0) /\
    (nxt <> -1 ->
      0 <= nxt < Zlength l /\
      xizi_single_link_wf nxt l /\
      1 + xizi_single_link_len_spec nxt l = xizi_single_link_len_spec node l).
Proof.
  intros node l Hwf.
  unfold xizi_single_link_wf in Hwf.
  destruct Hwf as [Hrange Hvalid].
  assert (HrangeZ : 0 <= node < Zlength l).
  { rewrite Zlength_correct. exact Hrange. }
  rewrite Nat2Z.id in Hvalid.
  split.
  - intro Hnxt.
    unfold xizi_single_link_len_spec.
    rewrite xizi_next_at_eq_Znth by exact HrangeZ.
    rewrite Hnxt.
    apply xizi_single_link_len_nat_neg1.
  - intro Hnxt.
    unfold xizi_single_link_len_spec in *.
    rewrite xizi_next_at_eq_Znth in Hvalid by exact HrangeZ.
    destruct l as [|a tl].
    + exfalso.
      rewrite Zlength_nil in HrangeZ.
      lia.
    + simpl in Hvalid.
      pose proof
        (xizi_single_link_valid_unfold (length tl) nil (Znth node (a :: tl) 0) (a :: tl) Hnxt Hvalid)
        as [Hnxt_range [Hfresh Htail]].
      assert (Hnxt_range_nat : 0 <= Znth node (a :: tl) 0 < Z.of_nat (length (a :: tl))).
      { rewrite <- Zlength_correct. exact Hnxt_range. }
      split.
      * exact Hnxt_range.
      * split.
        -- split.
           ++ exact Hnxt_range_nat.
           ++ rewrite Nat2Z.id.
              simpl.
              change (xizi_single_link_valid_nat (S (length tl)) nil
                (xizi_next_at (Znth node (a :: tl) 0) (a :: tl)) (a :: tl)).
              replace (S (length tl)) with (length tl + 1)%nat by lia.
              apply xizi_single_link_valid_increase_fuel with (extra := 1%nat).
              apply xizi_single_link_valid_weaken_seen with (seen_big := Znth node (a :: tl) 0 :: nil).
              ** intros x _. reflexivity.
              ** exact Htail.
        -- rewrite Nat2Z.id.
           rewrite (xizi_next_at_eq_Znth node (a :: tl)) by exact HrangeZ.
           unfold xizi_single_link_len_spec.
           replace (Datatypes.length (a :: tl)) with (S (Datatypes.length tl)) by reflexivity.
           pose proof (xizi_single_link_len_nat_valid_step
             (Datatypes.length tl) nil (Znth node (a :: tl) 0) (a :: tl)
             Hnxt Hvalid) as Hstep.
           lia.
Qed.

Lemma xizi_single_link_valid_len_bound :
  forall fuel seen node nexts,
    xizi_single_link_valid_nat fuel seen node nexts ->
    xizi_single_link_len_nat fuel node nexts <= Z.of_nat fuel.
Proof.
  induction fuel as [|fuel IH]; intros seen node nexts Hvalid; simpl in *.
  - lia.
  - destruct (Z.eq_dec node (-1)).
    + lia.
    + destruct Hvalid as [_ [_ Htail]].
      specialize (IH (node :: seen) (xizi_next_at node nexts) nexts Htail).
      change (1 + xizi_single_link_len_nat fuel (xizi_next_at node nexts) nexts <= Z.of_nat (S fuel)).
      replace (Z.of_nat (S fuel)) with (1 + Z.of_nat fuel) by lia.
      lia.
Qed.

Lemma xizi_single_link_wf_bound :
  forall node l,
    xizi_single_link_wf node l ->
    xizi_single_link_len_spec node l <= Zlength l.
Proof.
  intros node l Hwf.
  unfold xizi_single_link_wf in Hwf.
  destruct Hwf as [Hrange Hvalid].
  assert (HrangeZ : 0 <= node < Zlength l).
  { rewrite Zlength_correct. exact Hrange. }
  unfold xizi_single_link_len_spec.
  rewrite Nat2Z.id in Hvalid.
  rewrite Nat2Z.id.
  rewrite xizi_next_at_eq_Znth in Hvalid by exact HrangeZ.
  rewrite xizi_next_at_eq_Znth by exact HrangeZ.
  apply Z.le_trans with (m := Z.of_nat (length l)).
  - apply xizi_single_link_valid_len_bound with (seen := nil).
    exact Hvalid.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma proof_of_xizi_single_link_len_safety_wit_4 : xizi_single_link_len_safety_wit_4.
Proof.
  pre_process.
  entailer!.
  assert (0 <= xizi_single_link_len_spec node l).
  { unfold xizi_single_link_len_spec.
    apply xizi_single_link_spec_nonneg. }
  assert (xizi_single_link_len_spec head_pre l <= n).
  { pose proof (xizi_single_link_len_spec_bound_any head_pre l).
    lia. }
  match goal with
  | Hstep : node <> -1 ->
      length + 1 + xizi_single_link_len_spec node l =
      xizi_single_link_len_spec head_pre l |- _ =>
      specialize (Hstep H)
  end.
  lia.
Qed.

Lemma proof_of_xizi_single_link_len_entail_wit_1 : xizi_single_link_len_entail_wit_1.
Proof.
  pre_process.
  entailer!.
  - match goal with
    | Hwf : xizi_single_link_wf head_pre l |- _ =>
        destruct (xizi_single_link_wf_step head_pre l Hwf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [_ [_ Heq]].
    lia.
  - match goal with
    | Hwf : xizi_single_link_wf head_pre l |- _ =>
        destruct (xizi_single_link_wf_step head_pre l Hwf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [_ [Hwf _]].
    exact Hwf.
  - match goal with
    | Hwf : xizi_single_link_wf head_pre l |- _ =>
        destruct (xizi_single_link_wf_step head_pre l Hwf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [Hr _].
    lia.
  - match goal with
    | Hwf : xizi_single_link_wf head_pre l |- _ =>
        destruct (xizi_single_link_wf_step head_pre l Hwf) as [Hdone _]
    end.
    intro Hz.
    apply Hdone in Hz.
    lia.
Qed.

Lemma proof_of_xizi_single_link_len_entail_wit_2 : xizi_single_link_len_entail_wit_2.
Proof.
  pre_process.
  entailer!.
  - match goal with
    | Hwf_imp : node <> -1 -> xizi_single_link_wf node l |- _ =>
        pose proof (Hwf_imp H) as Hnode_wf;
        destruct (xizi_single_link_wf_step node l Hnode_wf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [_ [_ Heq]].
    match goal with
    | Hlen : node <> -1 ->
        length + 1 + xizi_single_link_len_spec node l =
        xizi_single_link_len_spec head_pre l |- _ =>
        specialize (Hlen H)
    end.
    lia.
  - match goal with
    | Hwf_imp : node <> -1 -> xizi_single_link_wf node l |- _ =>
        pose proof (Hwf_imp H) as Hnode_wf;
        destruct (xizi_single_link_wf_step node l Hnode_wf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [_ [Hwf _]].
    exact Hwf.
  - match goal with
    | Hwf_imp : node <> -1 -> xizi_single_link_wf node l |- _ =>
        pose proof (Hwf_imp H) as Hnode_wf;
        destruct (xizi_single_link_wf_step node l Hnode_wf) as [_ Hstep]
    end.
    intro Hz.
    destruct (Hstep Hz) as [Hr _].
    lia.
  - match goal with
    | Hwf_imp : node <> -1 -> xizi_single_link_wf node l |- _ =>
        pose proof (Hwf_imp H) as Hnode_wf;
        destruct (xizi_single_link_wf_step node l Hnode_wf) as [Hdone _]
    end.
    intro Hz.
    apply Hdone in Hz.
    match goal with
    | Hlen : node <> -1 ->
        length + 1 + xizi_single_link_len_spec node l =
        xizi_single_link_len_spec head_pre l |- _ =>
        specialize (Hlen H)
    end.
    lia.
  - assert (0 <= xizi_single_link_len_spec node l).
    { unfold xizi_single_link_len_spec.
      apply xizi_single_link_spec_nonneg. }
    assert (xizi_single_link_len_spec head_pre l <= n).
    { pose proof (xizi_single_link_len_spec_bound_any head_pre l).
      lia. }
    match goal with
    | Hlen : node <> -1 ->
        length + 1 + xizi_single_link_len_spec node l =
        xizi_single_link_len_spec head_pre l |- _ =>
        specialize (Hlen H)
    end.
    lia.
Qed.
