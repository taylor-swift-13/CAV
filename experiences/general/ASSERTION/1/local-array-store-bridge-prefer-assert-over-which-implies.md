# Local array store bridges should prefer direct `Assert` over `which implies`

Symptom:

- a loop owns a local stack array as
  `IntArray::seg(buf, 0, k, xs) * IntArray::undef_seg(buf, k, CAP)`;
- the next statement writes `buf[k] = ...`;
- a pre-store bridge written as `which implies` tries to expose
  `undef_data_at(buf + k * sizeof(int), int)` plus the trailing
  `IntArray::undef_seg`;
- `symexec` does not report an ordinary VC failure and instead crashes or exits
  immediately, while the same workspace stays stable if that bridge is removed.

Cause:

- for this local-array write pattern, `which implies` can be a parser/front-end
  instability point rather than a logical weakness;
- the intended ownership split is still valid, but the front end is more stable
  when the split is stated as a direct bridge assertion at the write site.

Rule:

- when a local fixed-size array needs a single-cell write bridge, prefer a flat
  direct `Assert` immediately before the store;
- keep the bridge in the final writable shape the next statement consumes:
  initialized prefix, one `undef_data_at(...)` cell, and the remaining
  `IntArray::undef_seg`;
- if a `which implies` bridge is the first annotation block that recreates a
  silent `symexec` crash, rewrite it as a direct `Assert` before changing the
  invariant or proof plan.

Minimal shape:

```c
/*@ Assert
      exists xs,
        0 <= k && k < CAP &&
        Zlength(xs) == k &&
        IntArray::seg(buf, 0, k, xs) *
        undef_data_at(buf + (k * sizeof(int)), int) *
        IntArray::undef_seg(buf, k + 1, CAP)
*/
buf[k] = v;
```

Do not start with:

```c
/*@ ... which implies
      exists xs,
        ...
        undef_data_at(buf + (k * sizeof(int)), int) *
        IntArray::undef_seg(buf, k + 1, CAP)
*/
```

Scope:

- parser/buffer builders and similar loops that append into a local stack array
  one element at a time;
- especially useful when the previous invariant already proved `k < CAP`, but
  the write still needs a one-cell ownership exposure before `buf[k] = ...`.
