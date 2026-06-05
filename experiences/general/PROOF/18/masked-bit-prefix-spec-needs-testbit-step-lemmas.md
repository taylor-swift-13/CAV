# Masked bit-prefix specs need a `land -> mod -> testbit-sum` proof bridge

Symptom:

- The loop invariant already has the right summary shape, for example
  `count == spec(score & ((1 << i) - 1))`.
- After `symexec`, the remaining VCs are pure preservation / return obligations for the two branches at bit `i`, but direct unfolding or `vm_compute` is brittle or too expensive.
- Typical stuck goals ask you to show:
  `spec(score & ((1 << (i + 1)) - 1)) = spec(score & ((1 << i) - 1)) + 0/1`
  and the branch fact arrives as `score & (signed_last_nbits (1 << i) 32) = 0` or `<> 0`.

Cause:

- The proof burden is not missing annotation information; it is the semantic bridge between executable masks and the task-local bit-count spec.
- QCP branch facts are phrased through `land` and `signed_last_nbits`, while the clean mathematical step is about whether `Z.testbit score i` is false or true.

Rule:

- Prove a small helper stack instead of unfolding the witness body:
  `signed_last_nbits (1 << i) 32 = 1 << i`;
  `score & ((1 << n) - 1) = score mod 2^n`;
  branch-mask nonzero/zero implies `Z.testbit score i = true/false`;
  and one prefix-step lemma turning the `(i + 1)` mask into the `i` mask plus `Z.b2z (Z.testbit score i)`.
- Use those helpers once in each branch witness, then finish with `simpl`, `ring_simplify`, or `lia`.
- For concrete base cases, prefer bounded unfolding and targeted rewrites over `vm_compute`.

Minimal shape:

```coq
Lemma land_low_mask_mod :
  Z.land score (Z.shiftl 1 n - 1) = score mod 2 ^ n.

Lemma signed_last_nbits_shiftl_eq :
  signed_last_nbits (Z.shiftl 1 i) 32 = Z.shiftl 1 i.

Lemma land_single_bit_nonzero_testbit :
  Z.land score (2 ^ i) <> 0 -> Z.testbit score i = true.

Lemma ex_allergies_score_count_prefix_step :
  spec (Z.land score (Z.shiftl 1 (i + 1) - 1)) =
  spec (Z.land score (Z.shiftl 1 i - 1)) +
  Z.b2z (Z.testbit score i).
```

Scope:

- `problem_kind = count`
- `data = scalar`
- `pattern = single_loop`
- Fixed-width bit-scan proofs where the spec counts contributions from a masked low-bit prefix and branch facts come from `score & (1 << i)`
