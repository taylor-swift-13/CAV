# Pointer-based string scans need a focused current-cell invariant at the loop head

Applicable shape:

- read-only null-terminated `char *` scan;
- loop guard directly dereferences the moving pointer, e.g. `while (*p != 0)`;
- loop body dereferences the same pointer again before incrementing it;
- executable code must stay text-identical, so rewriting to an index loop or `while (1) { ... break; }` is not available in verify.

Typical symptom:

- a coarse loop invariant that keeps only the whole buffer, e.g. `CharArray::full(s, n + 1, app(l, cons(0, nil)))`, can look semantically sufficient;
- but fresh `symexec` repeatedly fails at the loop guard or the next `*p` read with:

```text
fatal error: Cannot derive the precondition of Memory Read.
```

Cause:

- for this pointer-scan shape, `symexec` does not reliably reopen the currently focused byte from a coarse whole-array predicate at every guard/body dereference;
- a body-local `Assert` is too late if the first failing read is the guard itself.

Reusable rule:

- move the focus into the loop invariant itself;
- keep the array context as `CharArray::missing_i(...)`;
- keep the live byte at `p` as an explicit `store(p, char, ...)`;
- still preserve the prefix/position summary (`p == s + Zlength(l1)`, processed-prefix spec, bounds `0 <= Zlength(l1) <= n`, and any stable overflow fact such as `n < 2147483647`).

Stable loop-head shape:

```c
/*@ Inv Assert exists l1 l2,
      0 <= Zlength(l1) && Zlength(l1) <= n &&
      0 <= count && count <= Zlength(l1) &&
      n < 2147483647 &&
      s == s@pre &&
      p == s + Zlength(l1) &&
      l == app(l1, l2) &&
      Zlength(l) == n &&
      count == <prefix_spec>(l1) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::missing_i(s, Zlength(l1), 0, n + 1, app(l, cons(0, nil))) *
      store(p, char, Znth(Zlength(l1), app(l, cons(0, nil)), 0))
*/
```

Why this works:

- `missing_i` carries the unchanged string context;
- the explicit `store(p, ...)` gives the loop guard an immediate read permission at the real control point;
- after the `*p != 0` branch, the same focused byte can be advanced by the standard `missing_i_merge_to_full` / `full_split_to_missing_i` proof pattern.

Scope:

- `problem_kind = count`
- `data = string`
- `pattern = single_loop`
- more generally, any byte-wise pointer scan that repeatedly reads the current byte before `p++`
