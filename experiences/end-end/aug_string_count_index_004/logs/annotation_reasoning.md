# Annotation reasoning

## 2026-06-05 initial prefix-count invariant for `aug_string_count_index_004`

Phenomenon: the active annotated file `/home/yangfp/CAV/C/CAV/annotated/verify_20260605_041101v_aug_string_count_index_004.c` initially matched the input implementation and had no `Inv` before the single `while (1)` loop, so `symexec` failed with `Error: Lack of assertions in some paths for the loop!` at line 23. The loop reads `s[i]`, breaks on the null terminator, increments `count` exactly when `s[i] == 101`, then increments `i`.

Localization: the missing loop summary is at the only loop in `aug_string_count_index_004`, between local initialization `int count = 0; int i = 0;` and the final `return count;`.

Repair action: add a prefix/suffix invariant that keeps the read-only heap resource unchanged and summarizes the processed prefix with the Coq spec:

```c
/*@ Inv exists l1 l2,
      0 <= i && i <= n &&
      0 <= count && count <= i &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == i &&
      Zlength(l) == n &&
      count == aug_string_count_index_004_spec(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Why this invariant is the right shape: at the loop head, `i` is exactly the number of already processed non-terminator characters, so `l1` should be the processed prefix and `l2` the remaining suffix. The semantic state needed by the postcondition is `count == aug_string_count_index_004_spec(l1)`. The bounds `0 <= count <= i` are needed because `count++` can increase by at most one per processed character. The loop never writes memory, so the full resource remains `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, not a transformed heap predicate.

Initialization argument: choose `l1 = nil`, `l2 = l` at loop entry. Then `i == 0`, `count == 0`, `Zlength(nil) == 0`, `l == app(nil, l)`, and `aug_string_count_index_004_spec(nil) == 0`, while the unchanged pointer fact, nonzero payload fact, and heap resource come directly from the function precondition.

Preservation argument: on the continuing path, `s[i] != 0`. Combined with `CharArray::full(s, n + 1, app(l, cons(0, nil)))` and `(forall k, 0 <= k < n => l[k] != 0)`, this means the current position is still inside the payload and contributes one new element to the processed prefix. If that element equals `101`, `count++` matches the recursive `+ 1` branch of `aug_string_count_index_004_spec`; otherwise `count` stays unchanged, matching the `+ 0` branch. After `i++`, the next loop head again has `Zlength(l1) == i` for the extended prefix.

Exit bridge: add a minimal assertion immediately before `return count;`:

```c
/*@ Assert exists l1 l2,
      i == n &&
      0 <= count && count <= n &&
      s == s@pre &&
      l == app(l1, l2) &&
      Zlength(l1) == n &&
      Zlength(l) == n &&
      count == aug_string_count_index_004_spec(l) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
```

Why the exit assertion should close the return witness: if the loop breaks because `s[i] == 0`, the no-internal-zero contract excludes `i < n`, so `i == n`. Then `Zlength(l1) == n`, `Zlength(l) == n`, and `l == app(l1, l2)` force the remaining suffix `l2` to be empty, turning `count == aug_string_count_index_004_spec(l1)` into the exact postcondition relation `count == aug_string_count_index_004_spec(l)`. Placing the assertion immediately after the loop keeps local permissions in the standard loop-exit shape.
