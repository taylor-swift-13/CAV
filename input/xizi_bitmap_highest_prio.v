Require Import ZArith.

Open Scope Z_scope.

Definition xizi_bitmap_highest_prio_spec (bitmap r : Z) : Prop :=
  (bitmap = 0 /\ r = 0) \/
  (0 <= r < 32 /\
   Z.testbit bitmap r = true /\
   forall k : Z, r < k < 32 -> Z.testbit bitmap k = false).
