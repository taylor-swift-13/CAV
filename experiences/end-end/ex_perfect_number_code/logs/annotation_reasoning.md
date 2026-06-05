## 2026-06-05 20:15:10 +0800 - Initial loop summary for proper-divisor accumulation

Location: the only loop in [verify_20260605_200638v_ex_perfect_number_code.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c) is:

```c
for (int d = 1; d < n; d++) {
    if (n % d == 0) {
        sum += d;
    }
}
```

The active annotated copy initially had only the function contract. That is not enough for verification because the postcondition classifies `n` using `aliquot_sum_z(n)`, while the executable loop only leaves the scalar locals `sum` and `d`. The loop therefore needs a semantic relation that says “processed proper-divisor contribution plus unprocessed tail contribution equals the full aliquot sum”.

The imported Coq file defines:

```coq
Fixpoint aliquot_sum_from_fuel (n d : Z) (fuel : nat) : Z := ...
Definition aliquot_sum_z (n : Z) : Z :=
  aliquot_sum_from_fuel n 1 (Z.to_nat n).
```

Direct `Z.to_nat(...)` syntax is not parser-stable inside C annotations in this repo. Following the established `count_divisors` / `digit_product` pattern, I will add a workspace-local helper module under `coq/deps/`:

```coq
Definition aliquot_sum_tail_z (n d : Z) : Z :=
  aliquot_sum_from_fuel n d (Z.to_nat (n - d + 1)).
```

This gives a Z-arity tail summary for the remaining candidates `d, d + 1, ..., n - 1`. At the `for`-loop invariant control point, the initialized state has `d == 1`, `sum == 0`, and no divisor candidate has been processed, so the correct invariant equation is:

```c
sum + aliquot_sum_tail_z(n, d) == aliquot_sum_z(n@pre)
```

The full first invariant to add before the loop is:

```c
/*@ Inv
      0 < n &&
      n == n@pre &&
      1 <= d && d <= n &&
      0 <= sum &&
      0 <= aliquot_sum_tail_z(n, d) &&
      sum + aliquot_sum_tail_z(n, d) == aliquot_sum_z(n@pre)
*/
```

Why this should be sufficient:

- Initialization: before the first guard test, `d == 1` and `sum == 0`, so the semantic equality reduces to `aliquot_sum_tail_z(n, 1) == aliquot_sum_z(n)`. The helper definition makes this a direct unfolding because `n - 1 + 1 == n`. The contract already gives `0 < n`, and the tail sum is nonnegative because each recursive contribution is either `0` or the positive candidate `d`.
- Preservation: under the loop guard `d < n`, the loop body either leaves `sum` unchanged or adds exactly `d` when `n % d == 0`. That matches one recursive step of `aliquot_sum_tail_z(n, d)`. After the loop step `d++`, the next invariant point should re-establish the same equation with `d + 1`.
- Exit usability: when the loop exits, the invariant gives `d <= n` and the failed guard gives `d >= n`, so `d == n`. The helper tail at `d == n` is `0`, because the recursive definition immediately stops when `d >= n`. Therefore `sum == aliquot_sum_z(n@pre)`. A small exit assertion can then bridge directly to the three return branches.

To make the post-loop classification explicit while locals are still live, I will also add:

```c
/*@ Assert
      d == n &&
      n == n@pre &&
      sum == aliquot_sum_z(n@pre)
*/
```

This is the minimal bridge from loop exit to the two `if` comparisons and the final `return 3;`. It does not change the contract or executable code.

## 2026-06-05 20:17:03 +0800 - Loop-exit bridge must keep `d` in scope

The first `symexec` run failed before VC generation with:

```text
fatal error: Use of undeclared identifier `d' in /home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c:33:4
```

The annotated file used:

```c
for (int d = 1; d < n; d++) {
    ...
}

/*@ Assert
      d == n &&
      ...
*/
```

This is a front-end scope error, not a semantic invariant failure. In C, a variable declared in the `for` initializer is not available after the loop, so the exit bridge cannot mention it. The repair is to move `d` to a standalone local declaration before the loop:

```c
int d;
...
for (d = 1; d < n; d++) {
```

This preserves the executable behavior and keeps the loop-exit assertion aligned with the live local state.

## 2026-06-05 20:44:18 +0800 - Retry fix: remove helper import and recover exact executable loop form

Runner audit exposed two infrastructure-facing problems in the current annotated file:

```text
goal.v: Cannot find a physical path bound to logical path ex_perfect_number_code_helper
source integrity: annotated C changes executable implementation after removing comments/QCP annotations
```

Location: `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_200638v_ex_perfect_number_code.c`

The current annotation shape causing those failures is:

```c
/*@ Extern Coq (aliquot_sum_tail_z : Z -> Z -> Z) */
/*@ Import Coq Require Import ex_perfect_number_code_helper */
int d;
for (d = 1; d < n; d++) { ... }
/*@ Assert d == n && ... */
```

Why this must be changed instead of patched in replay:

- `experiences/general/SYMEXEC/README.md §19` explicitly warns that verify-stage helper imports can pass `symexec` but fail audit replay because generated files hard-code `Require Import <helper>.`
- the source-integrity gate compares executable code after stripping annotations, so changing `for (int d = 1; ... )` into `int d; for (d = 1; ... )` is not acceptable even if the C semantics are the same

Adopted replacement pattern:

```c
/*@ Extern Coq (aliquot_sum_from_fuel : Z -> Z -> nat -> Z) */
/* no helper import */
/*@ Inv
      0 < n &&
      n == n@pre &&
      1 <= d && d <= n &&
      0 <= sum &&
      0 <= aliquot_sum_from_fuel(n, d, Z.to_nat(n - d + 1)) &&
      sum + aliquot_sum_from_fuel(n, d, Z.to_nat(n - d + 1)) == aliquot_sum_z(n@pre)
*/
for (int d = 1; d < n; d++) { ... }
```

This keeps the executable implementation byte-for-byte aligned with the input loop form while using only symbols already defined in the input-stage Coq file `ex_perfect_number_code.v`. The post-loop bridge will also be reduced to facts over `sum` and `n@pre`, because `d` is not in scope after the original `for (int d = ...)` and the regenerated return VC should no longer require it.

The first helper-free replay failed immediately in `symexec` with:

```text
fatal error: Use of undeclared identifier `Z' in ...verify_20260605_200638v_ex_perfect_number_code.c:26:4
```

So this front-end does not accept `Z.to_nat(...)` syntax directly inside the loop invariant. I am therefore keeping the source-integrity fix (`for (int d = 1; ... )`) but reverting the invariant summary back to the already-working Z-arity wrapper `aliquot_sum_tail_z`. The remaining audit fix will be handled at the replay/load-path level for the helper module instead of forcing a parser-unstable helper-free annotation shape.
