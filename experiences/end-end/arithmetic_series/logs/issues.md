## Issue 1

- Phenomenon: the first `symexec` run failed with `fatal error: Expected loop after loop invariant.` instead of generating Coq obligations.
- Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_165821_arithmetic_series.c`, loop annotation for `while (i < n)` in `arithmetic_series`; failing run recorded in `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/logs/qcp_run.log`.
- Repair action: move the `/*@ Inv ... */` block so it appears immediately before `while (i < n)` rather than between `while (i < n)` and `{`.
- Key snippet:

```c
/*@ Inv
      0 <= i && i <= n &&
      a == a@pre && d == d@pre && n == n@pre &&
      cur == a + i * d &&
      sum == arithmetic_series_sum_z(a, d, i)
*/
while (i < n)
```

- Why this fix: the QCP frontend attaches loop invariants to the loop head control point; the interposed placement was parsed as malformed syntax, so witness generation could not start.

## Issue 2

- Phenomenon: `coqc` initially failed in `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/coq/generated/arithmetic_series_proof_manual.v` while proving the helper step lemma for `arithmetic_series_sum_z`, first with `Cannot find witness` and then with product-order rewrite mismatches around `/ 2`.
- Location: theorem `arithmetic_series_sum_z_step` in `arithmetic_series_proof_manual.v`.
- Repair action: replace the naive `lia` proof with an explicit divisibility-preserving rewrite using `Z.div_add`, and normalize the `i * d * 2 / 2` subterm with `Z.div_mul`.
- Key Coq snippet:

```coq
replace (d * (i + 1) * i) with (d * i * (i - 1) + (d * i) * 2) by lia.
rewrite Z.div_add by lia.
replace (i * d * 2 / 2) with (i * d).
2:{ symmetry. apply Z.div_mul. lia. }
```

- Why this fix: the closed form contains integer division, so `lia` alone does not expose the exact even numerator shape needed for the step relation at `i + 1`.

## Issue 3

- Phenomenon: several witness proofs failed with `Cannot find witness` even though the needed math facts were already implied by the contract and loop invariant.
- Location: theorems `proof_of_arithmetic_series_safety_wit_3`, `proof_of_arithmetic_series_safety_wit_4`, `proof_of_arithmetic_series_entail_wit_1`, and `proof_of_arithmetic_series_return_wit_1` in `arithmetic_series_proof_manual.v`.
- Repair action: stop relying on bare `entailer!`/`lia`, and first assert the exact witness-shaped facts: bounds for `sum + cur`, bounds for `cur + d_pre`, the initialization equality `0 = arithmetic_series_sum_z ... 0`, and the loop-exit equality `i = n_pre`. Preserve a copy of `arithmetic_series_pre ...` before destructing it in `entail_wit_1`.
- Key Coq snippets:

```coq
assert (Hint : int_min <= sum + cur <= int_max).
{
  rewrite H2, H3.
  exact Hsum.
}
```

```coq
pose proof Hpre as Hpre_keep.
...
assert (Heq : i = n_pre) by lia.
subst i.
```

- Why this fix: QCP entailment automation is sensitive to the exact RHS witness shape; once the proof state used the same expressions as the generated VC, `entailer!` closed the spatial/pure entailments reliably.

## Integrity

- `cmp` confirmed `/home/yangfp/CAV/C/CAV/input/arithmetic_series.c` matches `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/original/arithmetic_series.c` and `/home/yangfp/CAV/C/CAV/input/arithmetic_series.v` matches `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/original/arithmetic_series.v`.
- `diff -u` confirmed the only change from input C to `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_165821_arithmetic_series.c` is the added loop invariant; the function contract and executable statements are unchanged.
- Cleanup completed: `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/coq/` now contains only the four generated `.v` files, and no extra artifacts were present under `input/`.

Final Result: Success
