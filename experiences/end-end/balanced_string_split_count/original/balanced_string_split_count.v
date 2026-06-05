Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Definition lr_step (x : Z) : Z :=
  if Z.eq_dec x 76 then 1 else -1.

Fixpoint all_lr (l : list Z) : Prop :=
  match l with
  | nil => True
  | x :: xs => (x = 76 \/ x = 82) /\ all_lr xs
  end.

Fixpoint lr_balance (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => lr_step x + lr_balance xs
  end.

Fixpoint balanced_string_split_count_go (balance : Z) (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs =>
      let balance' := balance + lr_step x in
      (if Z.eq_dec balance' 0 then 1 else 0) +
      balanced_string_split_count_go balance' xs
  end.

Definition balanced_string_split_count_pre (l : list Z) : Prop :=
  all_lr l /\ lr_balance l = 0.

Definition balanced_string_split_count_spec (l : list Z) : Z :=
  balanced_string_split_count_go 0 l.
