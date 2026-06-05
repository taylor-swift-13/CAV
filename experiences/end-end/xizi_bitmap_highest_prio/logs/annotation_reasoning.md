2026-06-03 Round 1

Phenomenon: `xizi_bitmap_highest_prio` has a descending `for` loop with no verification annotations yet, so `symexec` cannot preserve the semantic fact needed by both return sites: once control reaches index `i`, every bit in `(i, 32)` has already been tested and found zero.

Location: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c`, loop `for (i = 31; i >= 0; --i)`.

Fix action: Add a loop invariant with three parts:
1. `-1 <= i && i <= 31` to match the loop-head control point, including skip/exit state `i == -1`.
2. `bitmap == bitmap@pre` to keep the return witness aligned with the postcondition over the original argument.
3. `forall (Z k), i < k && k < 32 => Z.testbit(bitmap@pre, k) == false` to summarize the already-processed suffix of higher-priority bits.

Key annotation fragment:

```c
/*@ Inv
      -1 <= i && i <= 31 &&
      bitmap == bitmap@pre &&
      forall (Z k),
        i < k && k < 32 =>
        Z.testbit(bitmap@pre, k) == false
*/
```

Why this change: At loop entry with `i == 31`, the quantified range is empty, so initialization is straightforward. If the `if` branch returns at index `i`, the branch guard gives the current bit is nonzero while the invariant already proves every higher bit is zero. If the loop exits with `i == -1`, the invariant yields all bits `0..31` are zero, which is the exact summary needed to prove the `bitmap = 0` postcondition for an unsigned 32-bit input.

2026-06-03 Round 2

Phenomenon: `symexec` stopped in the annotation parser before VC generation with `fatal error: bison: syntax error, unexpected PT_RPAREN, expecting PT_COLON` at the quantified binder inside the loop invariant.

Location: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c:18`.

Fix action: Replace the non-QCP binder syntax `forall (Z k)` with the parser-supported form `forall (k: Z)` seen in repository examples.

Key parser-compatible fragment:

```c
forall (k: Z),
  i < k && k < 32 =>
  Z.testbit(bitmap@pre, k) == false
```

Why this change: This is a front-end syntax correction only; it preserves the intended invariant semantics while allowing `symexec` to generate the actual verification conditions.

2026-06-03 Round 3

Phenomenon: After fixing the binder syntax, `symexec` still failed before VC generation with `Expected loop after loop invariant.` The parser rejected the invariant placement between the `for (...)` header and `{`.

Location: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c:22`.

Fix action: Move the invariant to the canonical QCP position immediately before the `for` statement and use the standard `Inv Assert` form seen in the allowed examples.

Key layout fragment:

```c
/*@ Inv Assert
    ...
*/
for (i = 31; i >= 0; --i) {
```

Why this change: This is another front-end alignment fix. It keeps the same semantic invariant but attaches it to the actual loop control point QCP expects for `for` loops.

2026-06-03 Round 4

Phenomenon: `symexec` still failed before VC generation with `Use of undeclared identifier 'Z'`. The failure is consistent with the known front-end limitation around qualified Coq identifiers inside loop annotations; the invariant currently mentions `Z.testbit(bitmap@pre, k)`.

Location: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c`, loop invariant pure clause.

Fix action: Replace the Coq-side bit predicate with an equivalent C-level assertion over shifts and masks:

```c
forall (k: Z),
  i < k && k < 32 =>
  (((bitmap@pre >> k) & 1u) == 0u)
```

Why this change: The loop semantics only require "bit `k` is clear." Expressing that with source-level unsigned operations avoids the front-end's qualified-name parser path while keeping the invariant aligned with the executable code. If `symexec` accepts this form, any remaining connection to `xizi_bitmap_highest_prio_spec` can be discharged in Coq proof rather than in the parser.

2026-06-03 Round 5

Phenomenon: After successful VC generation, the return obligations only retain the pure invariant facts. Without an explicit unsigned-range fact, the zero-bitmap return case is too weak: "all bits `0..31` are zero" does not imply `bitmap@pre = 0` for an arbitrary mathematical `Z`.

Location: Generated return witnesses from `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_goal.v`.

Fix action: Strengthen the loop invariant with the source-level unsigned range carried on the pre-state value:

```c
0 <= bitmap@pre && bitmap@pre <= UINT_MAX
```

Why this change: This does not alter the contract or executable code. It records a semantic fact already guaranteed by the C type of `bitmap`, and it is necessary so the exit witness can conclude that a 32-bit unsigned value with every bit `0..31` clear must be exactly zero.

2026-06-03 Round 6

Phenomenon: Compiling the regenerated VCs showed that putting `0 <= bitmap@pre && bitmap@pre <= UINT_MAX` directly into the invariant makes `entail_wit_1` try to prove the unsigned bound from bare `emp`, which is impossible. The type fact is only available while the local `bitmap` store is still present.

Location: loop prelude in `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c`; failed init witness in generated `xizi_bitmap_highest_prio_goal.v`.

Fix action: Insert a standalone local bridge immediately before the loop:

```c
/*@ 0 <= bitmap && bitmap <= UINT_MAX by local */
```

and keep the invariant range fact so later return witnesses can reuse it.

Why this change: This matches the documented `by local` idiom. The bound is derived from the live `unsigned int` local store at the correct control point, instead of being incorrectly demanded from the function precondition.
