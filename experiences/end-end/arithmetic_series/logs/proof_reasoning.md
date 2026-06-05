## Iteration 1

- Phenomenon: `coq/generated/arithmetic_series_proof_manual.v` contains five manual witness placeholders: `arithmetic_series_safety_wit_3`, `arithmetic_series_safety_wit_4`, `arithmetic_series_entail_wit_1`, `arithmetic_series_entail_wit_2`, and `arithmetic_series_return_wit_1`.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/coq/generated/arithmetic_series_goal.v` and `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/coq/generated/arithmetic_series_proof_manual.v`.
- Repair action: Prove all witness obligations directly from `arithmetic_series_pre` by unfolding the precondition, using the range facts for arithmetic-progression terms and partial sums, and adding one helper lemma for `arithmetic_series_sum_z (i + 1)`.
- Key Coq fragments:

```coq
Lemma arithmetic_series_sum_z_step :
  forall a d i,
    arithmetic_series_sum_z a d (i + 1) =
    arithmetic_series_sum_z a d i + (a + i * d).
```

```coq
unfold arithmetic_series_pre in Hpre.
destruct Hpre as [Hn [Hterm Hsum]].
specialize (Hsum (i + 1)).
assert (0 <= i + 1 <= n_pre) by lia.
```

- Why this fix: all remaining VCs are scalar equalities or integer-range side conditions. The contract already states closed-form bounds for every term and every prefix sum up to `n`, so the proof layer only needs to bridge the loop step and instantiate those quantified facts at `i` or `i + 1`.

## Iteration 2

- Phenomenon: initial `coqc` attempts failed on three fronts: the helper lemma for `arithmetic_series_sum_z` did not reduce through `/ 2`, safety witnesses could not find a witness until the RHS used `sum + cur` / `cur + d_pre` directly, and `entail_wit_1` temporarily lost the full `arithmetic_series_pre ...` predicate after destructing it.
- Location: `/home/yangfp/CAV/C/CAV/output/verify_20260604_165821_arithmetic_series/coq/generated/arithmetic_series_proof_manual.v`, helper lemma `arithmetic_series_sum_z_step`, theorems `proof_of_arithmetic_series_safety_wit_3`, `proof_of_arithmetic_series_safety_wit_4`, `proof_of_arithmetic_series_entail_wit_1`, and `proof_of_arithmetic_series_return_wit_1`.
- Repair action: rewrite the helper lemma with `Z.div_add`/`Z.div_mul`, assert witness-shaped bounds before `entailer!`, preserve `Hpre` with `pose proof`, and substitute the loop-exit equality `i = n_pre` before the return entailment.
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
assert (Heq : i = n_pre) by lia.
subst i.
```

- Why this fix: the generated VCs are solved once the proof state mirrors the exact symbolic-execution witness terms; proving more abstractly and hoping automation normalizes the terms was what caused the repeated `Cannot find witness` failures.
