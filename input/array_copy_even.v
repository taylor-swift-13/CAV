Require Import ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition list_nth_z (i : Z) (l : list Z) : Z :=
  nth (Z.to_nat i) l 0.

Fixpoint list_set_nat (k : nat) (v : Z) (l : list Z) : list Z :=
  match k, l with
  | O, [] => []
  | O, _ :: xs => v :: xs
  | S k', [] => []
  | S k', x :: xs => x :: list_set_nat k' v xs
  end.

Definition list_set_z (i : Z) (v : Z) (l : list Z) : list Z :=
  if Z.leb 0 i then list_set_nat (Z.to_nat i) v l else l.

Definition copy_even_value (x : Z) : Z :=
  if Z.even x then x else 0.

Fixpoint array_copy_even_region_aux
    (fuel : nat) (i src_off dst_off n : Z) (mem : list Z) : list Z :=
  match fuel with
  | O => mem
  | S fuel' =>
      if Z.ltb i n then
        array_copy_even_region_aux
          fuel'
          (i + 1)
          src_off
          dst_off
          n
          (list_set_z (dst_off + i)
             (copy_even_value (list_nth_z (src_off + i) mem))
             mem)
      else mem
  end.

Definition array_copy_even_region_spec
    (src_off dst_off n : Z) (mem : list Z) : list Z :=
  array_copy_even_region_aux (S (Z.to_nat n)) 0 src_off dst_off n mem.
