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

Definition problem_17_spec (input output : list Z) : Prop :=
  output = map Z.of_nat (parse_music_impl (string_of_list input)).

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
