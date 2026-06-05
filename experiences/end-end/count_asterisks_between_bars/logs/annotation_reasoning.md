2026-06-05 annotation iteration 1

Phenomenon: the annotated working copy had no loop invariant for the `while (1)` scan in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c`, so `symexec` would have no summary for the evolving scan state `inside`, the accumulator `count`, and the current index `i`.

Location: function `count_asterisks_between_bars`, loop over `s[i]`, with Coq spec `count_asterisks_between_bars_spec` and helper `count_asterisks_between_bars_go` from `/home/yangfp/CAV/C/CAV/input/count_asterisks_between_bars.v`.

Repair action: introduced a suffix-style invariant and a post-loop assertion. The invariant splits the logical string as `l == app(prefix, suffix)` with `Zlength(prefix) == i`, constrains `inside` to the two reachable states `0` and `1`, and preserves the key summary

`count + count_asterisks_between_bars_go(inside, suffix) == count_asterisks_between_bars_spec(l)`.

Key annotation fragment:

```c
/*@
  Inv exists prefix suffix,
        l == app(prefix, suffix) &&
        Zlength(prefix) == i &&
        0 <= i && i <= n &&
        (inside == 0 || inside == 1) &&
        count + count_asterisks_between_bars_go(inside, suffix) ==
          count_asterisks_between_bars_spec(l) &&
        CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Why this change: the loop is a one-pass state machine. A prefix-only invariant like `count == spec(prefix)` loses the pending `inside` state and cannot explain what should happen when the remainder starts inside a bar-delimited region. The suffix equation keeps exactly the state needed for the next character update and should collapse to the postcondition when the break proves `i == n`, since the remaining suffix is then empty.

2026-06-05 annotation iteration 2

Phenomenon: the first `symexec` run failed before VC generation with `fatal error: The number of now assertions and loop inv pre assertions does not match` at the loop header in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c:35`.

Location: loop invariant for `while (1)` in `count_asterisks_between_bars`.

Repair action: rewrote the boolean-state fact from a top-level disjunction to a range fact:

```c
0 <= inside && inside <= 1
```

replacing

```c
(inside == 0 || inside == 1)
```

Why this change: the frontend has prior failures on invariants that encode case splits directly inside one assertion. Here the loop state is still exactly the same two-value machine, but the flattened numeric range keeps it as a single assertion and avoids the annotation-case split that triggers the bookkeeping mismatch.

2026-06-05 annotation iteration 3

Phenomenon: reading the generated `count_asterisks_between_bars_return_wit_1` in `/home/yangfp/CAV/C/CAV/output/verify_20260605_054012v_count_asterisks_between_bars/coq/generated/count_asterisks_between_bars_goal.v` showed a concrete annotation loss. The premise carried `CharArray.full s ...` while the conclusion required `CharArray.full s_pre ...`, but the invariant had not preserved `s == s@pre`. The same invariant also gave no simple arithmetic bound on `count`, leaving `count + 1 <= INT_MAX` to be derived indirectly from the semantic recurrence.

Location: loop invariant and post-loop assertion in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c`.

Repair action: strengthened the annotation with two explicit facts:

```c
s == s@pre &&
0 <= count && count <= i &&
```

Why this change: `s` is a read-only parameter and should stay syntactically tied to its pre-state through the entire loop; otherwise the return witness becomes an avoidable proof obligation about heap relocation rather than function semantics. The `count <= i` fact captures the natural prefix bound of this scanner and turns the increment safety check into local arithmetic, which is exactly the kind of information that belongs in the invariant rather than being reconstructed later from the recursive spec.

2026-06-05 annotation iteration 4

Phenomenon: the near-final Coq replay isolated a real cutpoint loss in `count_asterisks_between_bars_return_wit_1`. After `pre_process; entailer!`, the only remaining goal was

```coq
count = count_asterisks_between_bars_spec l
```

from the premises

```coq
l = prefix ++ suffix
Zlength prefix = n
count + count_asterisks_between_bars_go inside suffix = count_asterisks_between_bars_spec l
```

but there was no longer any fact tying `Zlength l` back to `n`, so the proof could not derive `suffix = nil`.

Location: the explicit post-loop `Assert` in `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_054012v_count_asterisks_between_bars.c`.

Repair action: extended that exit assertion with the two dropped contract facts:

```c
Zlength(l) == n &&
(forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
```

Why this change: `Assert` is a semantic cutpoint, and everything omitted there is lost to the return witness. The proof obligation needed the original full-string length to show that once `i == n` and `Zlength(prefix) == i`, the remaining suffix must be empty. Restoring the contract facts at the exit cutpoint is the correct annotation-layer repair; trying to finish the proof without them would be unsound guesswork.
