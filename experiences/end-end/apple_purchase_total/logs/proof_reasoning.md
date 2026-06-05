# Proof Reasoning

## Round 1 — safety_wit_1

### Goal analysis

`apple_purchase_total_safety_wit_1`:

```
forall (price_pre: Z) (count_pre: Z),
  " (count_pre >= 0) " && " (price_pre >= 0) " && " ((count_pre * price_pre) <= INT_MAX) "
  && (&("price") # Int |-> price_pre) ** (&("count") # Int |-> count_pre)
|--
  " ((count_pre * price_pre) <= INT_MAX) " && " ((INT_MIN) <= (count_pre * price_pre)) "
```

Two conclusions to prove:
1. `count_pre * price_pre <= INT_MAX` — present verbatim in the LHS hypotheses.
2. `INT_MIN <= count_pre * price_pre` — follows from `count_pre >= 0` and `price_pre >= 0`: non-negative × non-negative ≥ 0, and INT_MIN = -2147483648 < 0 ≤ product.

Both are pure arithmetic; the spatial resources on the LHS (`|->` mapsto predicates) do not appear on the RHS and are simply dropped.

VC shape: straight-line scalar entail → tactic template `pre_process; entailer!; try lia.`

- `pre_process` unpacks the string-notation pure hypotheses into Z propositions.
- `entailer!` handles the pure/spatial split.
- `lia` closes both arithmetic subgoals.

No helper lemma needed. No structural induction, no list reasoning.

### Attempt 1 proof script

```coq
Lemma proof_of_apple_purchase_total_safety_wit_1 : apple_purchase_total_safety_wit_1.
Proof. pre_process; entailer!; try lia. Qed.
```

Will compile and report result below.
