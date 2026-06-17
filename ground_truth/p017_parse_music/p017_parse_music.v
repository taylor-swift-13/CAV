(* spec/17 *)
(* """ Input to this function is a string representing musical notes in a special ASCII format.
Your task is to parse this string and return list of integers corresponding to how many beats does each
not last.

Here is a legend:
'o' - whole note, lasts four beats
'o|' - half note, lasts two beats
'.|' - quater note, lasts one beat

>>> parse_music('o o| .| o| o| .| .| .| .| o o')
[4, 2, 1, 2, 2, 1, 1, 1, 1, 4, 4]
""" *)

(*
*)

Require Import Ascii String List.
Import ListNotations.
Open Scope string_scope.

Fixpoint SplitOnSpaces_aux (current_group : list ascii) (S : string) : list string :=
  match S with
  | EmptyString =>
    match current_group with
    | [] => []
    | _ => [string_of_list_ascii (List.rev current_group)]
    end
  | String h t =>
    if ascii_dec h " "%char then
      match current_group with
      | [] => SplitOnSpaces_aux [] t (* 多个或前导空格 *)
      | _ => (string_of_list_ascii (List.rev current_group)) :: SplitOnSpaces_aux [] t
      end
    else
      SplitOnSpaces_aux (h :: current_group) t
  end.

Definition SplitOnSpaces (S : string) : list string :=
  SplitOnSpaces_aux [] S.

Definition parse_note (note : string) : option nat :=
  if string_dec note "o" then Some 4
  else if string_dec note "o|" then Some 2
  else if string_dec note ".|" then Some 1
  else None.

Fixpoint parse_music_impl_aux (notes : list string) : list nat :=
  match notes with
  | [] => []
  | note :: rest =>
    match parse_note note with
    | Some n => n :: parse_music_impl_aux rest
    | None => parse_music_impl_aux rest
    end
  end.

Definition parse_music_impl (input : string) : list nat :=
  parse_music_impl_aux (SplitOnSpaces input).

(* Pre: no additional constraints for `parse_music` by default *)


Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.
From AUXLib Require Import ListLib.
Require Import string_bridge.

Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition problem_17_pre (input : list Z) : Prop :=
  True.

Definition ascii_range (s : list Z) : Prop :=
  forall i, 0 <= i < Zlength s -> 0 <= Znth i s 0 <= 127.

Definition note_state_step (state ch : Z) : Z :=
  if Z.eqb ch 32 then 0
  else if Z.eqb state 0 then
    if Z.eqb ch 111 then 1
    else if Z.eqb ch 46 then 3
    else 5
  else if Z.eqb state 1 then
    if Z.eqb ch 124 then 2 else 5
  else if Z.eqb state 3 then
    if Z.eqb ch 124 then 4 else 5
  else 5.

Definition music_step_state : Z -> Z -> Z := note_state_step.

Definition music_final_output (out : list Z) (state : Z) : list Z :=
  if Z.eqb state 1 then out ++ [4]
  else if Z.eqb state 2 then out ++ [2]
  else if Z.eqb state 4 then out ++ [1]
  else out.

Definition music_step_output (out : list Z) (state ch : Z) : list Z :=
  if Z.eqb ch 32 then music_final_output out state else out.

Fixpoint music_scan_aux (chars out : list Z) (state : Z) : list Z * Z :=
  match chars with
  | [] => (out, state)
  | ch :: rest =>
      music_scan_aux rest
        (music_step_output out state ch)
        (note_state_step state ch)
  end.

Definition music_prefix_output (i : Z) (input : list Z) : list Z :=
  fst (music_scan_aux (sublist 0 i input) [] 0).

Definition music_prefix_state (i : Z) (input : list Z) : Z :=
  snd (music_scan_aux (sublist 0 i input) [] 0).

Definition music_output (input : list Z) : list Z :=
  let scanned := music_scan_aux input [] 0 in
  music_final_output (fst scanned) (snd scanned).

Definition problem_17_spec (input output : list Z) : Prop :=
  output = music_output input.

Fixpoint list_z_of_ascii (l : list ascii) : list Z :=
  match l with
  | [] => []
  | c :: rest => Z.of_nat (nat_of_ascii c) :: list_z_of_ascii rest
  end.

Definition z_of_note_state (state : Z) : option Z :=
  if Z.eqb state 1 then Some 4
  else if Z.eqb state 2 then Some 2
  else if Z.eqb state 4 then Some 1
  else None.

Definition token_state_rev (current_group : list Z) : Z :=
  fold_left note_state_step (rev current_group) 0.

Definition token_output (current_group : list Z) : list Z :=
  music_final_output [] (token_state_rev current_group).

Fixpoint split_music_z_aux (current_group input : list Z) : list Z :=
  match input with
  | [] => token_output current_group
  | ch :: rest =>
      if Z.eqb ch 32 then
        token_output current_group ++ split_music_z_aux [] rest
      else
        split_music_z_aux (ch :: current_group) rest
  end.

Definition parse_note_output_nat (note : string) : list nat :=
  match parse_note note with
  | Some n => [n]
  | None => []
  end.

Definition no_space_z_list (l : list Z) : Prop :=
  forall ch, In ch l -> ch <> 32.

Local Opaque string_dec.

Lemma music_prefix_full_final : forall input len,
  len = Zlength input ->
  music_final_output
    (music_prefix_output len input)
    (music_prefix_state len input) =
  music_output input.
Proof.
  intros input len Hlen.
  unfold music_prefix_output, music_prefix_state, music_output.
  rewrite (sublist_self input len Hlen).
  reflexivity.
Qed.

Lemma music_scan_aux_step : forall prefix ch out state,
  music_scan_aux (prefix ++ [ch]) out state =
  let scanned := music_scan_aux prefix out state in
  (music_step_output (fst scanned) (snd scanned) ch,
   note_state_step (snd scanned) ch).
Proof.
  induction prefix as [| h t IH]; intros ch out state; simpl.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Lemma music_prefix_step : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output (i + 1) input =
    music_step_output
      (music_prefix_output i input)
      (music_prefix_state i input)
      (Znth i input 0) /\
  music_prefix_state (i + 1) input =
    note_state_step
      (music_prefix_state i input)
      (Znth i input 0).
Proof.
  intros input i Hi.
  unfold music_prefix_output, music_prefix_state.
  assert (sublist 0 (i + 1) input = sublist 0 i input ++ [Znth i input 0]) as Hsub.
  {
    rewrite (sublist_split 0 (i + 1) i input) by lia.
    rewrite (sublist_single 0 i input) by lia.
    reflexivity.
  }
  rewrite Hsub.
  rewrite music_scan_aux_step.
  split; reflexivity.
Qed.

Lemma music_prefix_step_app : forall input i,
  0 <= i < Zlength input ->
  music_prefix_output (i + 1) input =
    music_step_output
      (music_prefix_output i input)
      (music_prefix_state i input)
      (Znth i (app input (cons 0 nil)) 0) /\
  music_prefix_state (i + 1) input =
    note_state_step
      (music_prefix_state i input)
      (Znth i (app input (cons 0 nil)) 0).
Proof.
  intros input i Hi.
  pose proof (music_prefix_step input i Hi) as [Hout Hstate].
  replace (Znth i (app input (cons 0 nil)) 0) with (Znth i input 0).
  - split; assumption.
  - rewrite app_Znth1; lia.
Qed.

Lemma note_state_step_range : forall state ch,
  0 <= state <= 5 ->
  0 <= note_state_step state ch <= 5.
Proof.
  intros state ch Hstate.
  unfold note_state_step.
  destruct (Z.eqb ch 32) eqn:?; [lia |].
  destruct (Z.eqb state 0) eqn:?.
  - destruct (Z.eqb ch 111) eqn:?; [lia |].
    destruct (Z.eqb ch 46) eqn:?; lia.
  - destruct (Z.eqb state 1) eqn:?.
    + destruct (Z.eqb ch 124) eqn:?; lia.
    + destruct (Z.eqb state 3) eqn:?.
      * destruct (Z.eqb ch 124) eqn:?; lia.
      * lia.
Qed.

Lemma music_step_space_skip : forall out state,
  state <> 1 -> state <> 2 -> state <> 4 ->
  music_step_output out state 32 = out /\
  note_state_step state 32 = 0.
Proof.
  intros out state H1 H2 H4.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 2) H2).
  rewrite (proj2 (Z.eqb_neq state 4) H4).
  split; reflexivity.
Qed.

Lemma music_step_space_1 : forall out,
  music_step_output out 1 32 = out ++ [4] /\
  note_state_step 1 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  split; reflexivity.
Qed.

Lemma music_step_space_2 : forall out,
  music_step_output out 2 32 = out ++ [2] /\
  note_state_step 2 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 2 1) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_space_4 : forall out,
  music_step_output out 4 32 = out ++ [1] /\
  note_state_step 4 32 = 0.
Proof.
  intros out.
  unfold music_step_output, music_final_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 4 1) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 4 2) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_o : forall out,
  music_step_output out 0 111 = out /\
  note_state_step 0 111 = 1.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 111 32) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_dot : forall out,
  music_step_output out 0 46 = out /\
  note_state_step 0 46 = 3.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 46 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 46 111) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_1_bar : forall out,
  music_step_output out 1 124 = out /\
  note_state_step 1 124 = 2.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_3_bar : forall out,
  music_step_output out 3 124 = out /\
  note_state_step 3 124 = 4.
Proof.
  intros out.
  unfold music_step_output, note_state_step.
  repeat rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq 124 32) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_3_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output out 3 ch = out /\
  note_state_step 3 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 3 0) ltac:(lia)).
  rewrite (proj2 (Z.eqb_neq 3 1) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_1_bad : forall out ch,
  ch <> 32 -> ch <> 124 ->
  music_step_output out 1 ch = out /\
  note_state_step 1 ch = 5.
Proof.
  intros out ch Hspace Hbar.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 124) Hbar).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_0_bad : forall out ch,
  ch <> 32 -> ch <> 111 -> ch <> 46 ->
  music_step_output out 0 ch = out /\
  note_state_step 0 ch = 5.
Proof.
  intros out ch Hspace Ho Hdot.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite Z.eqb_refl.
  rewrite (proj2 (Z.eqb_neq ch 111) Ho).
  rewrite (proj2 (Z.eqb_neq ch 46) Hdot).
  split; reflexivity.
Qed.

Lemma music_step_nonspace_other_bad : forall out state ch,
  ch <> 32 -> state <> 0 -> state <> 1 -> state <> 3 ->
  music_step_output out state ch = out /\
  note_state_step state ch = 5.
Proof.
  intros out state ch Hspace H0 H1 H3.
  unfold music_step_output, note_state_step.
  rewrite (proj2 (Z.eqb_neq ch 32) Hspace).
  rewrite (proj2 (Z.eqb_neq state 0) H0).
  rewrite (proj2 (Z.eqb_neq state 1) H1).
  rewrite (proj2 (Z.eqb_neq state 3) H3).
  split; reflexivity.
Qed.
