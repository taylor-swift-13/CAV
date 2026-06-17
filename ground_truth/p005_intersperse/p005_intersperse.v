Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Fixpoint intersperse_list (input : list Z) (d : Z) : list Z :=
  match input with
  | nil => nil
  | x :: nil => x :: nil
  | x :: xs => x :: d :: intersperse_list xs d
  end.

Lemma intersperse_list_snoc_nonempty : forall l x d,
  l <> nil ->
  intersperse_list (l ++ [x]) d = intersperse_list l d ++ [d; x].
Proof.
  intros l x d Hnonempty.
  destruct l as [| a xs]; [contradiction Hnonempty; reflexivity |].
  clear Hnonempty.
  revert a.
  induction xs as [| b xs IH]; intros a; simpl; auto.
  destruct xs as [| c xs].
  - reflexivity.
  - change (a :: d :: intersperse_list ((b :: c :: xs) ++ [x]) d =
            a :: d :: (intersperse_list (b :: c :: xs) d ++ [d; x])).
    rewrite (IH b). reflexivity.
Qed.

Lemma intersperse_list_sublist_one : forall l d,
  0 < Z.of_nat (length l) ->
  intersperse_list (sublist 0 1 l) d = [Znth 0 l 0].
Proof.
  intros.
  change 1 with (0 + 1).
  rewrite (sublist_single 0 0 l) by (rewrite Zlength_correct; lia).
  reflexivity.
Qed.

Lemma intersperse_list_sublist_snoc : forall l i d,
  1 <= i < Z.of_nat (length l) ->
  intersperse_list (sublist 0 (i + 1) l) d =
  intersperse_list (sublist 0 i l) d ++ [d; Znth i l 0].
Proof.
  intros.
  rewrite (sublist_split 0 (i + 1) i l) by (try rewrite Zlength_correct in *; lia).
  rewrite (sublist_single 0 i l) by (rewrite Zlength_correct; lia).
  apply intersperse_list_snoc_nonempty.
  intro Hempty.
  pose proof (Zlength_sublist 0 i l).
  assert (0 <= 0 <= i /\ i <= Zlength l) by (rewrite Zlength_correct; lia).
  specialize (H0 H1).
  rewrite Hempty in H0.
  rewrite Zlength_correct in H0.
  simpl in H0.
  lia.
Qed.

Lemma intersperse_list_length : forall (l : list Z) d,
  l <> nil ->
  Zlength (intersperse_list l d) = 2 * Zlength l - 1.
Proof.
  induction l as [| x xs IH]; intros d Hne.
  - contradiction.
  - destruct xs as [| y ys].
    + cbn [intersperse_list]. rewrite !Zlength_cons. simpl. lia.
    + assert (Hne' : y :: ys <> nil) by discriminate.
      specialize (IH d Hne').
      cbn [intersperse_list].
      change (match ys with
              | [] => [y]
              | _ :: _ => y :: d :: intersperse_list ys d
              end) with (intersperse_list (y :: ys) d).
      rewrite !Zlength_cons.
      rewrite IH.
      rewrite !Zlength_cons.
      lia.
Qed.
