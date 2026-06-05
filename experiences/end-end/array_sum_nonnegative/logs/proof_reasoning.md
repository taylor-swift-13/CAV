## Iteration 1

Phenomenon: After regenerating witnesses with the strengthened invariant, `proof_manual.v` still contains five admitted obligations: `array_sum_nonnegative_safety_wit_4`, `array_sum_nonnegative_entail_wit_1`, `array_sum_nonnegative_entail_wit_2_1`, `array_sum_nonnegative_entail_wit_2_2`, and `array_sum_nonnegative_return_wit_1`.

Location: `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_proof_manual.v` and the matching witness definitions in `.../array_sum_nonnegative_goal.v`.

Fix action: Reuse the verified `count_positive` / `array_count_negative` proof pattern for read-only array prefix scans. Add local helper lemmas for:

```coq
array_sum_nonnegative_spec (l ++ [x])
array_sum_nonnegative_spec (l1 ++ l2)
0 <= array_sum_nonnegative_spec l
array_sum_nonnegative_spec (sublist 0 i l) <= array_sum_nonnegative_spec l
```

Then discharge:
- `entail_wit_1` by `entailer!`
- branch entailments by rewriting `sublist 0 (i + 1) l` into the old prefix plus a singleton and simplifying one spec step
- `return_wit_1` by deriving `i = n_pre`, rewriting `sublist 0 n_pre l` to `l`, and finishing by reflexivity
- `safety_wit_4` by rewriting `sum + Znth i l 0` as the next prefix spec and bounding that prefix by the full-list spec from the precondition

Why this change: The generated VCs are pure list/arithmetic obligations. The annotation is already aligned with control flow, so adding proof-local helper lemmas is cheaper and more stable than another annotation round.

## Iteration 2

Phenomenon: The first `coqc` replay failed in `array_sum_nonnegative_spec_prefix_le` at `/home/yangfp/CAV/C/CAV/output/verify_20260605_010426v_array_sum_nonnegative/coq/generated/array_sum_nonnegative_proof_manual.v:65`. The script tried `rewrite <- (sublist_self 0 l) at 2`, and Coq reported `The term "0" has type "Z" while it is expected to have type "list ?A"`.

Location: helper lemma `array_sum_nonnegative_spec_prefix_le` in `.../array_sum_nonnegative_proof_manual.v`.

Fix action: Replace the incorrect explicit application of `sublist_self` with a direct `replace l with (sublist 0 (Zlength l) l) at 2` followed by `rewrite sublist_self; reflexivity`.

Key proof fragment:

```coq
replace l with (sublist 0 (Zlength l) l) at 2.
2:{ rewrite sublist_self; reflexivity. }
```

Why this change: The proof only needs the canonical whole-list prefix form so `sublist_split` can apply. Using `sublist_self` as a rewrite on the concrete term is stable; partially applying it with the wrong argument order is not.

## Iteration 3

Phenomenon: The next `coqc` failure was still in `proof_of_array_sum_nonnegative_safety_wit_4` at `.../array_sum_nonnegative_proof_manual.v:89`. I had specialized `Hle` with `H0`, but after `pre_process` that hypothesis name referred to `i < n_pre`, not to the newly asserted prefix-range fact.

Location: `proof_of_array_sum_nonnegative_safety_wit_4` in `.../array_sum_nonnegative_proof_manual.v`.

Fix action: Name the generated range fact explicitly as `Hrange` and specialize the monotonicity lemma with that named hypothesis instead of relying on positional auto-names.

Key proof fragment:

```coq
assert (Hrange : 0 <= i + 1 <= Zlength l) by lia.
specialize (Hle Hrange).
```

Why this change: `pre_process` produces unstable hypothesis numbering and short auto-names. Explicitly naming the derived range fact makes the helper application robust across recompiles and witness shape changes.

## Iteration 4

Phenomenon: `coqc` next failed at `.../array_sum_nonnegative_proof_manual.v:107` with `Found no subterm matching "sublist 0 (i + 1) l" in the current goal.` Inspecting `proof_of_array_sum_nonnegative_entail_wit_2_1` in `coqtop` showed that `entailer!` leaves two goals: first the upper-bound side condition `sum + Znth i l 0 <= INT_MAX`, then the semantic equality on `sublist 0 (i + 1) l`.

Location: `proof_of_array_sum_nonnegative_entail_wit_2_1` in `.../array_sum_nonnegative_proof_manual.v`.

Fix action: Split the proof into two bullets. Discharge the first goal with the same prefix-monotonicity argument used in `safety_wit_4`, and only then rewrite `sublist 0 (i + 1) l` in the second equality goal.

Key proof fragment:

```coq
entailer!.
- ... prove sum + Znth i l 0 <= INT_MAX via prefix_le ...
- subst sum.
  rewrite (sublist_split 0 (i + 1) i l) by lia.
```

Why this change: The earlier script assumed the equality goal was first. After `entailer!`, the actual goal order matters; proving the arithmetic side condition first prevents a rewrite against the wrong target.

## Iteration 5

Phenomenon: `coqc` then failed in `proof_of_array_sum_nonnegative_return_wit_1` at `.../array_sum_nonnegative_proof_manual.v:148` with `Found no subterm matching "2147483647" in the current goal.` The return proof was still using copied hypothesis names (`H2`, `H4`) from another case, but after `entailer!` the only remaining goal is `sum = array_sum_nonnegative_spec l`, and the length equation is carried by `H6`, not by the copied slot.

Location: `proof_of_array_sum_nonnegative_return_wit_1` in `.../array_sum_nonnegative_proof_manual.v`.

Fix action: Replace hard-coded hypothesis-number rewrites with structural `match goal` rewrites: first rewrite the goal with the current `sum = ...sublist...` fact, then rewrite `n_pre` to `Zlength l`, then apply `sublist_self`.

Key proof fragment:

```coq
match goal with
| Hsum : sum = _ |- _ => rewrite Hsum
end.
match goal with
| Hlen : Zlength l = n_pre |- _ => rewrite <- Hlen
end.
rewrite sublist_self by reflexivity.
```

Why this change: The witness is semantically straightforward once `i = n_pre` is derived. Matching the needed hypotheses by shape makes the script stable even when `pre_process` or `entailer!` renumber assumptions.
