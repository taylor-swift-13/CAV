Iteration 1

Phenomenon: `symexec` failed with `Error: Lack of assertions in some paths for the loop!` at [annotated/verify_20260605_043229v_balanced_string_split_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_043229v_balanced_string_split_count.c:26). The loop had no `Inv`, so symbolic execution had no loop-head summary.

Location: `balanced_string_split_count` loop at the `while (1)` control point.

Repair action: add a loop invariant that models the loop as a prefix scan over `l`. The state variables are:
- `i`: length of the processed prefix, so `0 <= i <= n`
- `balance`: the running `L/R` balance of `sublist 0 i l`
- `count`: the number of completed balanced pieces already counted, expressed with a suffix-style equation `count + balanced_string_split_count_go balance (sublist i n l) == balanced_string_split_count_spec(l)`

Key annotation shape:
```c
/*@ Inv
      s == s@pre &&
      0 <= i && i <= n &&
      balanced_string_split_count_pre(l) &&
      balance == lr_balance(sublist(0, i, l)) &&
      count + balanced_string_split_count_go(balance, sublist(i, n, l))
        == balanced_string_split_count_spec(l)
*/
```

Why this change: the invariant is written at the real loop-head control point and preserves exactly the semantic summary needed for exit. When `i == n`, the suffix becomes `nil`, so the equation collapses to `count == balanced_string_split_count_spec(l)` after proving `balanced_string_split_count_go balance nil = 0`.

Iteration 2

Phenomenon: after `symexec` succeeded, the generated manual VC still contained arithmetic safety obligations for `balance + 1`, `balance - 1`, and `count + 1` in `balanced_string_split_count_safety_wit_{7,8,11,12}`. Those facts are true by the scan structure, but without explicit numeric bounds they would have to be reconstructed from list semantics in Coq.

Location: the same loop invariant in [annotated/verify_20260605_043229v_balanced_string_split_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_043229v_balanced_string_split_count.c:28).

Repair action: strengthen the invariant with cheap numeric summaries:
```c
0 <= count && count <= i &&
-i <= balance && balance <= i
```

Why this change: for a prefix of length `i`, the count of completed balanced pieces cannot exceed `i`, and the running balance changes by exactly `+1` or `-1` per processed character, so it stays within `[-i, i]`. These facts are stable under the loop body and let the generated safety VCs collapse to `lia` instead of requiring list-level helper lemmas.

Iteration 3

Phenomenon: the generated `return_wit_1` in [balanced_string_split_count_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260605_043229v_balanced_string_split_count/coq/generated/balanced_string_split_count_goal.v:574) had precondition `emp` but postcondition `CharArray.full ...`, which is not a proof problem. It means the loop-exit `Assert` cut away the string ownership.

Location: the exit bridge assertion after the loop in [annotated/verify_20260605_043229v_balanced_string_split_count.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_043229v_balanced_string_split_count.c:47).

Repair action: include `CharArray::full(s, n + 1, app(l, cons(0, nil)))` in the exit `Assert`, not just the pure equalities.

Why this change: `Assert` is a semantic cut point for `symexec`. Any fact or resource omitted there is unavailable to later witnesses. The function postcondition needs the original string ownership, so the exit assertion must explicitly preserve that spatial fact.
