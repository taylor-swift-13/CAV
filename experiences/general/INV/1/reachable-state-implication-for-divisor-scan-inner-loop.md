# Reachable-state implication for divisor-scan inner loops

For scalar nested loops that scan candidate divisors in an outer loop and repeatedly divide in an inner loop, a residual-state invariant like

```c
count + rest_spec(n, d) == total_spec(n@pre)
```

is often necessary but not always sufficient. If the inner loop head is guarded only by `n % d == 0`, the generated VC may admit arithmetic states that satisfy divisibility and the basic bounds, but are unreachable from the real algorithm. Those fake models can break the one-step residual equation even though the executable loop is correct.

Typical symptom:

- `symexec` succeeds and leaves a small number of arithmetic/manual VCs;
- an inner-loop preservation witness still fails;
- the failing premise allows states like "current `d` divides `n`, but the outer-loop search invariant that made this state reachable is gone".

Reusable fix:

- keep the residual summary invariant;
- add the missing reachable-state fact to the inner invariant as an implication tied to the divisible branch.

For divisor scans of the form

```c
for (d = 2; d <= n / d; d++) {
    while (n % d == 0) {
        ...
        n /= d;
    }
}
```

a stable shape is:

```c
((n % d == 0) && (n != d) => d <= n / d)
```

Why this works:

- if the next inner-loop head is still divisible by `d`, then either `n == d` (last remaining factor) or the reduced state must still satisfy the outer-loop guard;
- carrying that implication removes unreachable arithmetic models from the VC;
- the proof then matches the real control-state semantics instead of an over-approximation built only from `%` and loose inequalities.

Use this pattern when:

- the algorithm repeatedly divides or peels factors inside an inner loop;
- the outer loop provides a search-bound fact that is needed again after one inner iteration;
- the failing VC is not missing a generic arithmetic lemma, but a fact about which divisible states are actually reachable.

Do not generalize this mechanically to unrelated nested loops. The point is to preserve the specific search-state constraint that makes the inner divisible state executable, not to add arbitrary implications to force a proof through.
