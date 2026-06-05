# When a loop-phase transition already carries a live local store, do not re-add `has_permission(&var)` in the next invariant (2026-06-05)

Symptom:

- `symexec` has already moved through one loop that leaves a live local such as `same`, `k`, or another stack scalar in scope;
- the next loop or bridge assertion preserves the same scalar again with an explicit `has_permission(&var)`;
- fresh replay then stops at the phase transition with a partial-solve failure such as:

```text
dup_data_at_error(var_addr)
Sep cannot be fully solved
```

Cause:

- across loop boundaries, QCP may already represent the live local as its normal stack `store(...)` / temp state;
- adding `has_permission(&var)` in the next invariant duplicates that same cell in `SEP`, so the failure is about **local-cell ownership duplication**, not about the pure arithmetic or array facts in the new loop.

Rule:

- when a new loop begins immediately after a previous loop that already kept a live local in scope, inspect the partial-solve dump before adding more permissions;
- if the failing `SEP` reduces to `dup_data_at_error(<var_addr>)`, remove the redundant `has_permission(&var)` from the new invariant and any bridge assertions around that phase;
- keep the pure facts about the variable if they are still needed, but preserve the cell only once.

Minimal pattern:

```c
while (k < sl) {
    if (!same) break;
    ...
}

k = 0;
/* wrong: next phase duplicates the same local cell */
/*@ Inv Assert
      ...
      has_permission(&same) *
      IntArray::full(cur, k, repeat_Z(0, k)) *
      IntArray::undef_seg(cur, k, 26)
*/
while (k < 26) {
    cur[k] = 0;
    k++;
}
```

Repair:

- remove `has_permission(&same)` from the zeroing-loop invariant and nearby `Assert` / `which implies` bridges;
- keep only the semantic facts that matter, for example `same == 0 || same == 1` or `(same != 0) => ...`;
- rerun `symexec` to expose the next real write/read obligation.

Why this matters:

- otherwise long verify runs can burn multiple retries on fake ownership noise after the real blocker has already been localized;
- the partial-solve trace is usually precise enough to tell you the duplicated cell name, so treat this as a phase-transition hygiene fix, not as a proof problem.

Scope:

- `problem_kind = count`
- `data = string`
- `pattern = nested_loop`
- especially nested scanners with reused stack locals that flow from a compare loop into an array-initialization or counting loop
