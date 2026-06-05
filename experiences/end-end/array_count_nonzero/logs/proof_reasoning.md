2026-06-05 iteration 1

Phenomenon: `symexec` on `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_000102v_array_count_nonzero.c` succeeded and generated manual obligations in `/home/yangfp/CAV/C/CAV/output/verify_20260605_000102v_array_count_nonzero/coq/generated/array_count_nonzero_proof_manual.v`: `proof_of_array_count_nonzero_safety_wit_4`, `proof_of_array_count_nonzero_entail_wit_1`, `proof_of_array_count_nonzero_entail_wit_2_1`, `proof_of_array_count_nonzero_entail_wit_2_2`, and `proof_of_array_count_nonzero_return_wit_1`.

Location: `array_count_nonzero_goal.v`, witness definitions `array_count_nonzero_safety_wit_4`, `array_count_nonzero_entail_wit_1`, `array_count_nonzero_entail_wit_2_1`, `array_count_nonzero_entail_wit_2_2`, `array_count_nonzero_return_wit_1`.

Repair action: Prove the witnesses in `array_count_nonzero_proof_manual.v` with a small set of helper lemmas:

- the spec on any list is between `0` and its length, to discharge `count + 1 <= INT_MAX` from `count = array_count_nonzero_spec (sublist 0 i l)` and `i < n`;
- the spec on `sublist 0 (i + 1) l` is the old prefix spec plus either `1` or `0` depending on `Znth i l 0`, to discharge the two branch entailments;
- the full-list postcondition follows from `i >= n`, `i <= n`, and `Zlength l = n_pre`, so the return witness reduces to the full-prefix case.

Key witness fragment:

```coq
“ ((count + 1) <= INT_MAX) ”
```

and

```coq
“ ((count + 1) = array_count_nonzero_spec (sublist 0 (i + 1) l)) ”
```

Why this change: The loop invariant already preserves the right semantic summary. The remaining obligations are exactly the standard proof-layer facts about how the recursive spec behaves when a single array element is appended to the processed prefix, plus a range bound showing the count of nonzero elements in a prefix cannot exceed the prefix length.
