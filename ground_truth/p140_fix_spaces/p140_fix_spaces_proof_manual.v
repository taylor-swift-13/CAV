Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.CAV.ground_truth_p140_fix_spaces Require Import p140_fix_spaces_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Require Import Lia.
From AUXLib Require Import ListLib.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Require Import Coq.Strings.Ascii.

Import naive_C_Rules.
Require Import string_bridge.
Require Import p140_fix_spaces.
Local Open Scope sac.
Local Open Scope list_scope.

(* Proof helpers moved from p140_fix_spaces.v so public contract files expose definitions only. *)

Lemma list_nonzero_app : forall a b,
  list_nonzero a ->
  list_nonzero b ->
  list_nonzero (a ++ b).
Proof.
  unfold list_nonzero.
  intros a b Ha Hb k Hk.
  rewrite Zlength_app in Hk.
  destruct (Z_lt_ge_dec k (Zlength a)).
  - rewrite app_Znth1 by lia.
    apply Ha; lia.
  - rewrite app_Znth2 by lia.
    apply Hb; lia.
Qed.
Lemma list_nonzero_single : forall x,
  x <> 0 ->
  list_nonzero [x].
Proof.
  unfold list_nonzero.
  intros x Hx k Hk.
  rewrite Zlength_cons, Zlength_nil in Hk.
  replace k with 0 by lia.
  simpl.
  exact Hx.
Qed.
Lemma list_ascii_of_string_string_of_list : forall l,
  list_ascii_of_string (string_of_list l) = map ascii_of l.
Proof.
  induction l as [| c rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma nat_of_ascii_ascii_of : forall z,
  0 <= z < 256 ->
  nat_of_ascii (ascii_of z) = Z.to_nat z.
Proof.
  intros z Hz.
  unfold ascii_of.
  apply nat_ascii_embedding.
  lia.
Qed.
Lemma flush_spaces_length : forall n,
  0 <= n ->
  Zlength (flush_spaces n) = flush_spaces_len n.
Proof.
  intros n Hn.
  unfold flush_spaces, flush_spaces_len.
  destruct (Z.eqb_spec n 0); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 1); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 2); subst; simpl; [reflexivity |].
  reflexivity.
Qed.
Lemma flush_spaces_len_bound : forall n,
  0 <= n -> flush_spaces_len n <= n.
Proof.
  intros n Hn.
  unfold flush_spaces_len.
  destruct (Z.eqb_spec n 0); subst; simpl; [lia |].
  destruct (Z.eqb_spec n 1); subst; simpl; [lia |].
  destruct (Z.eqb_spec n 2); subst; simpl; [lia |].
  lia.
Qed.
Lemma fix_spaces_state_0 : forall s,
  fix_spaces_prefix 0 s = [] /\
  fix_spaces_pending 0 s = 0.
Proof.
  intros s.
  unfold fix_spaces_prefix, fix_spaces_pending, fix_spaces_state.
  simpl.
  split; reflexivity.
Qed.
Lemma fold_left_scan_step_app : forall xs ys st,
  fold_left scan_step (xs ++ ys) st =
  fold_left scan_step ys (fold_left scan_step xs st).
Proof.
  induction xs as [| x xs IH]; intros ys st; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma firstn_succ_snoc_140 : forall {A : Type} n (l : list A) d,
  (n < List.length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n.
  - intros l d Hn. destruct l; simpl in *; try lia. reflexivity.
  - intros l d Hn. destruct l; simpl in *; try lia.
    rewrite (IHn l d) by lia. reflexivity.
Qed.
Lemma firstn_succ_Znth_140 : forall (l : list Z) i,
  0 <= i < Zlength l ->
  firstn (Z.to_nat (i + 1)) l =
  firstn (Z.to_nat i) l ++ [Znth i l 0].
Proof.
  intros l i H.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite firstn_succ_snoc_140 with (d := 0).
  - reflexivity.
  - apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.
Lemma fix_spaces_state_step : forall i s,
  0 <= i < Zlength s ->
  fix_spaces_state (i + 1) s =
  scan_step (fix_spaces_state i s) (Znth i s 0).
Proof.
  intros i s H.
  unfold fix_spaces_state.
  rewrite firstn_succ_Znth_140 by lia.
  rewrite fold_left_scan_step_app.
  reflexivity.
Qed.
Lemma fix_spaces_step_space : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 = 32 ->
  fix_spaces_prefix (i + 1) s = fix_spaces_prefix i s /\
  fix_spaces_pending (i + 1) s = fix_spaces_pending i s + 1.
Proof.
  intros i s Hi Hc.
  unfold fix_spaces_prefix, fix_spaces_pending.
  rewrite fix_spaces_state_step by lia.
  unfold scan_step.
  rewrite Hc.
  change (Z.eqb 32 32) with true.
  destruct (fix_spaces_state i s).
  split; reflexivity.
Qed.
Lemma fix_spaces_step_nonspace : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_prefix (i + 1) s =
    fix_spaces_prefix i s ++ flush_spaces (fix_spaces_pending i s) ++ [Znth i s 0] /\
  fix_spaces_pending (i + 1) s = 0.
Proof.
  intros i s Hi Hc.
  unfold fix_spaces_prefix, fix_spaces_pending.
  rewrite fix_spaces_state_step by lia.
  unfold scan_step.
  destruct (Z.eqb_spec (Znth i s 0) 32); [contradiction |].
  destruct (fix_spaces_state i s).
  split; reflexivity.
Qed.
Lemma fix_spaces_state_bound : forall i s,
  0 <= i ->
  i <= Zlength s ->
  0 <= fix_spaces_pending i s /\
  Zlength (fix_spaces_prefix i s) + fix_spaces_pending i s <= i.
Proof.
  intros i s Hi.
  remember (Z.to_nat i) as ni eqn:Hni.
  revert i Hi Hni.
  induction ni as [| ni IH]; intros i Hi Hni Hile.
  - assert (i = 0) by lia.
    subst i.
    destruct (fix_spaces_state_0 s) as [Hp Hpend].
    rewrite Hp, Hpend, Zlength_nil.
    lia.
  - assert (0 < i) by lia.
    pose (j := i - 1).
    assert (Hj_nonneg : 0 <= j) by (unfold j; lia).
    assert (Hj_len : j < Zlength s) by (unfold j; lia).
    assert (Hj_to_nat : Z.to_nat j = ni) by (unfold j; lia).
    specialize (IH j Hj_nonneg ltac:(symmetry; exact Hj_to_nat) ltac:(unfold j; lia)).
    destruct IH as [Hpend_nonneg Hbound].
    assert (Hi_eq : i = j + 1) by (unfold j; lia).
    rewrite Hi_eq.
    destruct (Z.eq_dec (Znth j s 0) 32) as [Hspace | Hnonspace].
    + destruct (fix_spaces_step_space j s ltac:(lia) Hspace) as [Hp Hpend].
      rewrite Hp, Hpend.
      lia.
    + destruct (fix_spaces_step_nonspace j s ltac:(lia) Hnonspace) as [Hp Hpend].
      rewrite Hp, Hpend.
      rewrite !Zlength_app, flush_spaces_length, Zlength_cons, Zlength_nil by lia.
      pose proof (flush_spaces_len_bound (fix_spaces_pending j s) Hpend_nonneg).
      lia.
Qed.
Lemma fix_spaces_prefix_bound : forall i s,
  0 <= i ->
  i <= Zlength s ->
  Zlength (fix_spaces_prefix i s) <= i.
Proof.
  intros i s Hi Hile.
  pose proof (fix_spaces_state_bound i s Hi Hile) as [Hpend Hbound].
  lia.
Qed.
Lemma fix_spaces_output_length_bound : forall s,
  Zlength (fix_spaces_output s) <= Zlength s.
Proof.
  intros s.
  unfold fix_spaces_output.
  rewrite Zlength_app, flush_spaces_length.
  - pose proof (fix_spaces_state_bound (Zlength s) s ltac:(apply Zlength_nonneg) ltac:(lia))
      as [Hpend Hbound].
    pose proof (flush_spaces_len_bound (fix_spaces_pending (Zlength s) s) Hpend).
    lia.
  - pose proof (fix_spaces_state_bound (Zlength s) s ltac:(apply Zlength_nonneg) ltac:(lia))
      as [Hpend _].
    exact Hpend.
Qed.
Lemma fix_spaces_step_nonspace_pending0 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending i s = 0 ->
  fix_spaces_prefix (i + 1) s =
    fix_spaces_prefix i s ++ [Znth i s 0] /\
  fix_spaces_pending (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split; [reflexivity | exact Hpend].
Qed.
Lemma fix_spaces_step_nonspace_pending1 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending i s = 1 ->
  fix_spaces_prefix (i + 1) s =
    (fix_spaces_prefix i s ++ [95]) ++ [Znth i s 0] /\
  fix_spaces_pending (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split; [rewrite <- app_assoc; reflexivity | exact Hpend].
Qed.
Lemma fix_spaces_step_nonspace_pending2 : forall i s,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  fix_spaces_pending i s = 2 ->
  fix_spaces_prefix (i + 1) s =
    ((fix_spaces_prefix i s ++ [95]) ++ [95]) ++ [Znth i s 0] /\
  fix_spaces_pending (i + 1) s = 0.
Proof.
  intros i s Hi Hc Hpending.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hp Hpend].
  rewrite Hp, Hpending.
  simpl.
  split.
  - repeat rewrite <- app_assoc; reflexivity.
  - exact Hpend.
Qed.
Lemma fix_spaces_step_nonspace_pending_more : forall i s p,
  0 <= i < Zlength s ->
  Znth i s 0 <> 32 ->
  p = fix_spaces_pending i s ->
  p > 2 ->
  fix_spaces_prefix (i + 1) s =
    (fix_spaces_prefix i s ++ [45]) ++ [Znth i s 0] /\
  fix_spaces_pending (i + 1) s = 0.
Proof.
  intros i s p Hi Hc Hp Hmore.
  destruct (fix_spaces_step_nonspace i s Hi Hc) as [Hpref Hpend].
  rewrite Hpref.
  rewrite <- Hp.
  unfold flush_spaces.
  destruct (Z.eqb_spec p 0); try lia.
  destruct (Z.eqb_spec p 1); try lia.
  destruct (Z.eqb_spec p 2); try lia.
  split; [rewrite <- app_assoc; reflexivity | exact Hpend].
Qed.
Lemma fix_spaces_output_pending0 : forall s,
  fix_spaces_pending (Zlength s) s = 0 ->
  fix_spaces_output s = fix_spaces_prefix (Zlength s) s.
Proof.
  intros s Hpending.
  unfold fix_spaces_output.
  rewrite Hpending.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.
Lemma fix_spaces_output_pending1 : forall s,
  fix_spaces_pending (Zlength s) s = 1 ->
  fix_spaces_output s = fix_spaces_prefix (Zlength s) s ++ [95].
Proof.
  intros s Hpending.
  unfold fix_spaces_output.
  rewrite Hpending.
  reflexivity.
Qed.
Lemma fix_spaces_output_pending2 : forall s,
  fix_spaces_pending (Zlength s) s = 2 ->
  fix_spaces_output s = fix_spaces_prefix (Zlength s) s ++ [95; 95].
Proof.
  intros s Hpending.
  unfold fix_spaces_output.
  rewrite Hpending.
  simpl.
  reflexivity.
Qed.
Lemma fix_spaces_output_pending_more : forall s p,
  p = fix_spaces_pending (Zlength s) s ->
  p > 2 ->
  fix_spaces_output s = fix_spaces_prefix (Zlength s) s ++ [45].
Proof.
  intros s p Hp Hmore.
  unfold fix_spaces_output.
  rewrite <- Hp.
  unfold flush_spaces.
  destruct (Z.eqb_spec p 0); try lia.
  destruct (Z.eqb_spec p 1); try lia.
  destruct (Z.eqb_spec p 2); try lia.
  reflexivity.
Qed.
Lemma ascii_of_space_iff : forall c,
  0 <= c < 256 ->
  ascii_of c = space <-> c = 32.
Proof.
  intros c Hrange.
  split; intros H.
  - apply (f_equal nat_of_ascii) in H.
    rewrite nat_of_ascii_ascii_of in H by lia.
    vm_compute in H.
    change 32%nat with (Z.to_nat 32) in H.
    apply Z2Nat.inj in H; lia.
  - subst c. reflexivity.
Qed.
Lemma string_of_list_flush_spaces : forall n,
  0 <= n ->
  string_of_list (flush_spaces n) =
  string_of_list_ascii (flush_spaces_nat (Z.to_nat n)).
Proof.
  intros n Hn.
  unfold flush_spaces, flush_spaces_nat.
  destruct (Z.eqb_spec n 0); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 1); subst; simpl; [reflexivity |].
  destruct (Z.eqb_spec n 2); subst; simpl; [reflexivity |].
  destruct (Z.to_nat n) as [| [| [| m]]] eqn:Hnat; try lia.
  reflexivity.
Qed.
Lemma string_of_list_app_140 : forall a b,
  string_of_list (a ++ b) =
  (string_of_list a ++ string_of_list b)%string.
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_of_list_ascii_app_140 : forall a b,
  string_of_list_ascii (a ++ b) =
  (string_of_list_ascii a ++ string_of_list_ascii b)%string.
Proof.
  induction a as [| x xs IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma string_append_assoc_140 : forall a b c,
  ((a ++ b) ++ c = a ++ (b ++ c))%string.
Proof.
  induction a as [| ch rest IH]; intros b c; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.
Lemma fix_spaces_scan_correct_aux : forall s out pending,
  ascii_range s ->
  0 <= pending ->
  string_of_list
    (fst (fold_left scan_step s (out, pending)) ++
     flush_spaces (snd (fold_left scan_step s (out, pending)))) =
  (string_of_list out ++
   string_of_list_ascii (fix_spaces_scan (map ascii_of s) (Z.to_nat pending)))%string.
Proof.
  induction s as [| c rest IH]; intros out pending Hrange Hpending.
  - simpl.
    rewrite string_of_list_app_140.
    rewrite string_of_list_flush_spaces by lia.
    reflexivity.
  - simpl map.
    assert (Hc_range : 0 <= c < 256).
    {
      specialize (Hrange 0 ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg rest); lia)).
      change (Znth 0 (c :: rest) 0) with c in Hrange.
      lia.
    }
    assert (Hrest_range : ascii_range rest).
    {
      intros i Hi.
      specialize (Hrange (i + 1)).
      replace (Znth i rest 0) with (Znth (i + 1) (c :: rest) 0).
      - apply Hrange. rewrite Zlength_cons. pose proof (Zlength_nonneg rest); lia.
      - unfold Znth. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
        reflexivity.
    }
    destruct (Z.eq_dec c 32) as [Hspace | Hnonspace].
    + subst c.
      replace (ascii_of 32) with space by reflexivity.
      destruct (Ascii.ascii_dec space space) as [_ | Hbad]; [| contradiction].
      simpl.
      rewrite IH by (assumption || lia).
      replace (S (Z.to_nat pending)) with (Z.to_nat (pending + 1)) by lia.
      reflexivity.
    + assert (Hascii_nonspace : ascii_of c <> space).
      { intro Hbad. apply ascii_of_space_iff in Hbad; lia. }
      destruct (Ascii.ascii_dec (ascii_of c) space) as [Hbad | _].
      { contradiction. }
      simpl.
      replace (Z.eqb c 32) with false by (symmetry; apply Z.eqb_neq; exact Hnonspace).
      rewrite IH by (assumption || lia).
      rewrite !string_of_list_app_140.
      rewrite string_of_list_flush_spaces by lia.
      destruct (Ascii.ascii_dec (ascii_of c) space) as [Hbad2 | _];
        [contradiction |].
      destruct (Z.to_nat pending) as [| [| [| m]]] eqn:Hpn; simpl;
        rewrite ?string_append_assoc_140; reflexivity.
Qed.
Lemma fix_spaces_scan_correct : forall s,
  ascii_range s ->
  string_of_list (fix_spaces_output s) =
  string_of_list_ascii (fix_spaces_scan (map ascii_of s) 0).
Proof.
  intros s Hrange.
  unfold fix_spaces_output, fix_spaces_prefix, fix_spaces_pending,
         fix_spaces_state.
  replace (Z.to_nat (Zlength s)) with (length s) by
    (rewrite Zlength_correct; rewrite Nat2Z.id; reflexivity).
  rewrite firstn_all.
  change 0%nat with (Z.to_nat 0).
  rewrite fix_spaces_scan_correct_aux by (assumption || lia).
  reflexivity.
Qed.
Lemma problem_140_spec_intro : forall input output,
  ascii_range input ->
  output = fix_spaces_output input ->
  problem_140_spec input output.
Proof.
  intros input output Hrange Hout.
  unfold problem_140_spec, problem_140_spec, fix_spaces.
  rewrite Hout.
  rewrite list_ascii_of_string_string_of_list.
  rewrite fix_spaces_scan_correct by assumption.
  reflexivity.
Qed.


Ltac solve_fix_pending :=
  match goal with
  | H : fix_spaces_pending ?i ?l = ?p |- fix_spaces_pending ?i ?l = ?p =>
      exact H
  | H : ?p = fix_spaces_pending ?i ?l |- fix_spaces_pending ?i ?l = ?p =>
      symmetry; exact H
  | Hstate : ?sp = fix_spaces_pending ?i ?l,
    Hval : ?sp = ?p |- fix_spaces_pending ?i ?l = ?p =>
      rewrite <- Hstate; exact Hval
  | Hstate : ?sp = fix_spaces_pending ?i ?l,
    Hval : ?p = ?sp |- fix_spaces_pending ?i ?l = ?p =>
      rewrite <- Hstate; symmetry; exact Hval
  | Hstate : fix_spaces_pending ?i ?l = ?sp,
    Hval : ?sp = ?p |- fix_spaces_pending ?i ?l = ?p =>
      rewrite Hstate; exact Hval
  | Hstate : fix_spaces_pending ?i ?l = ?sp,
    Hval : ?p = ?sp |- fix_spaces_pending ?i ?l = ?p =>
      rewrite Hstate; symmetry; exact Hval
  end.

Ltac derive_out_nonzero :=
  unfold list_nonzero; intros ? ?;
  match goal with
  | H : forall j : Z, 0 <= j /\ j < Zlength ?out -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  | Hlen : ?k = Zlength ?out,
    H : forall j : Z, 0 <= j /\ j < ?k -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  | Hlen : Zlength ?out = ?k,
    H : forall j : Z, 0 <= j /\ j < ?k -> Znth j ?out 0 <> 0 |- _ =>
      apply H; lia
  end.

Ltac solve_ascii_range_char :=
  try solve [lia];
  match goal with
  | Hrange : ascii_range ?l |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hrange : forall j : Z, 0 <= j < Zlength ?l -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hlen : Zlength ?l = ?len,
    Hrange : forall j : Z, 0 <= j < ?len -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  | Hlen : ?len = Zlength ?l,
    Hrange : forall j : Z, 0 <= j < ?len -> 0 <= Znth j ?l 0 <= 127
    |- context[Znth ?idx ?l 0] =>
      pose proof (Hrange idx ltac:(lia)); lia
  end.

Ltac solve_input_char_nonzero :=
  match goal with
  | |- Znth ?i ?l 0 <> 0 =>
      match goal with
      | H : forall j : Z, 0 <= j /\ j < Zlength l -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      | Hlen : Zlength l = ?len,
        H : forall j : Z, 0 <= j /\ j < ?len -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      | Hlen : ?len = Zlength l,
        H : forall j : Z, 0 <= j /\ j < ?len -> Znth j l 0 <> 0 |- _ =>
          apply H; lia
      end
  | |- ?x <> 0 => lia
  end.

Ltac solve_list_nonzero_fact :=
  repeat apply list_nonzero_app;
  try derive_out_nonzero;
  try (apply list_nonzero_single; solve_input_char_nonzero);
  try (apply list_nonzero_single; lia).

Ltac solve_list_nonzero_goal :=
  match goal with
  | |- list_nonzero _ =>
      solve_list_nonzero_fact
  | |- forall j : Z, 0 <= j < ?bound -> Znth j ?out 0 <> 0 =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : list_nonzero out) by solve_list_nonzero_fact;
      unfold list_nonzero in Hnz;
      intros j Hj; apply Hnz;
      rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia
  | |- forall j : Z, 0 <= j /\ j < ?bound -> Znth j ?out 0 <> 0 =>
      let Hnz := fresh "Hnz" in
      assert (Hnz : list_nonzero out) by solve_list_nonzero_fact;
      unfold list_nonzero in Hnz;
      intros j Hj; apply Hnz;
      rewrite ?Zlength_app, ?Zlength_cons, ?Zlength_nil; lia
  end.

Lemma proof_of_p140_fix_spaces_entail_wit_1 : p140_fix_spaces_entail_wit_1.
Proof.
  unfold p140_fix_spaces_entail_wit_1.
  intros.
  pre_process.
  subst retval_2.
  Exists (@nil Z).
  destruct (fix_spaces_state_0 l) as [Hp Hpend].
  sep_apply (CharArray.undef_full_split_to_undef_seg retval 0 (len + 1)).
  rewrite (CharArray.undef_seg_empty retval 0).
  rewrite (CharArray.full_empty retval 0).
  entailer!.
  - lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_1 : p140_fix_spaces_entail_wit_2_1.
Proof.
  unfold p140_fix_spaces_entail_wit_2_1.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  Exists out_l_2.
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_space i l ltac:(lia) ltac:(assumption)) as [Hp _].
    symmetry; exact Hp.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_2 : p140_fix_spaces_entail_wit_2_2.
Proof.
  unfold p140_fix_spaces_entail_wit_2_2.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  assert (Hsp0 : spacelen = 0) by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists (out_l_2 ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending0 i l ltac:(lia) ltac:(assumption) ltac:(exact Hsp0))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_3 : p140_fix_spaces_entail_wit_2_3.
Proof.
  unfold p140_fix_spaces_entail_wit_2_3.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists ((out_l_2 ++ cons 45 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2.
    destruct (fix_spaces_step_nonspace_pending_more i l spacelen ltac:(lia) ltac:(assumption) ltac:(assumption) ltac:(lia))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_4 : p140_fix_spaces_entail_wit_2_4.
Proof.
  unfold p140_fix_spaces_entail_wit_2_4.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists (((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending2 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_entail_wit_2_5 : p140_fix_spaces_entail_wit_2_5.
Proof.
  unfold p140_fix_spaces_entail_wit_2_5.
  intros.
  pre_process.
  repeat rewrite app_Znth1 in * by lia.
  rewrite (signed_last_nbits_eq (Znth i l 0) 8) by solve_ascii_range_char.
  Exists ((out_l_2 ++ cons 95 nil) ++ cons (Znth i l 0) nil).
  entailer!.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [_ Hpend].
    symmetry; exact Hpend.
  - subst out_l_2 spacelen.
    destruct (fix_spaces_step_nonspace_pending1 i l ltac:(lia) ltac:(assumption) ltac:(solve_fix_pending))
      as [Hp _].
    symmetry; exact Hp.
  - solve_list_nonzero_goal.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_1 : p140_fix_spaces_return_wit_1.
Proof.
  unfold p140_fix_spaces_return_wit_1.
  intros.
  pre_process.
  assert (Hsp0 : spacelen = 0) by lia.
  Exists out_l_2 k_3.
  entailer!.
  - subst out_l_2.
    apply problem_140_spec_intro.
    + assumption.
    + 
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending0.
    match goal with
    | H : spacelen = fix_spaces_pending ?j l |- _ =>
        replace (fix_spaces_pending (Zlength l) l) with (fix_spaces_pending j l)
          by (replace j with (Zlength l) by lia; reflexivity);
        rewrite <- H; exact Hsp0
    | H : fix_spaces_pending ?j l = spacelen |- _ =>
        replace (fix_spaces_pending (Zlength l) l) with (fix_spaces_pending j l)
          by (replace j with (Zlength l) by lia; reflexivity);
        rewrite H; exact Hsp0
    end.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_2 : p140_fix_spaces_return_wit_2.
Proof.
  unfold p140_fix_spaces_return_wit_2.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 45 nil) (k_3 + 1).
  entailer!.
  subst out_l_2.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending_more with (p := spacelen).
    + replace (fix_spaces_pending (Zlength l) l)
        with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
      match goal with
      | H : spacelen = fix_spaces_pending i l |- _ => exact H
      end.
    + lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_3 : p140_fix_spaces_return_wit_3.
Proof.
  unfold p140_fix_spaces_return_wit_3.
  intros.
  pre_process.
  Exists ((out_l_2 ++ cons 95 nil) ++ cons 95 nil) ((k_3 + 1) + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    rewrite fix_spaces_output_pending2.
    2:{
      replace (fix_spaces_pending (Zlength l) l)
        with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
      solve_fix_pending.
    }
    rewrite <- app_assoc.
    reflexivity.
  - rewrite !Zlength_app, !Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.

Lemma proof_of_p140_fix_spaces_return_wit_4 : p140_fix_spaces_return_wit_4.
Proof.
  unfold p140_fix_spaces_return_wit_4.
  intros.
  pre_process.
  Exists (out_l_2 ++ cons 95 nil) (k_3 + 1).
  entailer!.
  subst out_l_2 spacelen.
  apply problem_140_spec_intro.
  - assumption.
  -
    replace i with (Zlength l) by lia.
    symmetry.
    apply fix_spaces_output_pending1.
    replace (fix_spaces_pending (Zlength l) l)
      with (fix_spaces_pending i l) by (replace i with (Zlength l) by lia; reflexivity).
    match goal with
    | H : 1 = fix_spaces_pending i l |- _ =>
        symmetry; exact H
    end.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
  - solve_list_nonzero_goal.
Qed.
