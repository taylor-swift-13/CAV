Require Import ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint defang_ip_address_spec (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: xs =>
      if Z.eq_dec x 46 then
        91 :: 46 :: 93 :: defang_ip_address_spec xs
      else
        x :: defang_ip_address_spec xs
  end.
