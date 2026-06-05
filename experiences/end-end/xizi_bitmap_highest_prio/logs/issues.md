2026-06-03 Summary

Phenomenon: The first annotation attempt failed before VC generation because the invariant used unsupported front-end shapes: binder syntax `forall (Z k)`, invariant placement between `for (...)` and `{`, and the qualified Coq identifier `Z.testbit` inside the annotation.

Location: `/home/yangfp/CAV/OS/CAV/annotated/verify_20260603_204428v_xizi_bitmap_highest_prio.c`, loop annotation; `symexec` errors recorded in `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/logs/qcp_run.log`.

Fix action: Rewrote the invariant to the accepted QCP layout and syntax:
- moved it to the canonical `/*@ Inv Assert ... */` position before the `for`
- changed the binder to `forall (k: Z)`
- replaced `Z.testbit(bitmap@pre, k)` with the C-level bit fact `((bitmap@pre >> k) & 1u) == 0u`

Key fragment:

```c
/*@ Inv Assert
      -1 <= i && i <= 31 &&
      bitmap == bitmap@pre &&
      0 <= bitmap@pre && bitmap@pre <= UINT_MAX &&
      forall (k: Z),
        i < k && k < 32 =>
        (((bitmap@pre >> k) & 1u) == 0u)
*/
```

Why this worked: It preserved the intended loop meaning while matching the parser and symbolic executor's supported surface language.

2026-06-03 Range-carry fix

Phenomenon: Carrying `0 <= bitmap@pre && bitmap@pre <= UINT_MAX` in the invariant was necessary for the zero-return proof, but the first attempt made the initialization witness try to derive that bound from bare `emp`.

Location: generated `xizi_bitmap_highest_prio_goal.v`, initial entailment witness after the first range-strengthening attempt.

Fix action: Added a pre-loop local bridge instead of demanding the bound from the precondition:

```c
/*@ 0 <= bitmap && bitmap <= UINT_MAX by local */
```

Why this worked: The unsigned bound is available from the live local store of `bitmap`; after this bridge, `symexec` regenerated witnesses where the range facts were available automatically and the manual proof set shrank to the three semantic theorems.

2026-06-03 Proof completion

Phenomenon: The remaining manual VCs were `entail_wit_3`, `return_wit_1`, and `return_wit_2`, all requiring translation between generated bitwise facts and the imported Coq spec.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/xizi_bitmap_highest_prio_proof_manual.v`.

Fix action: Added local helper lemmas for:
- `Z.land x 1 = 0 <->` bit-0 clear
- `Z.land x (Z.shiftl 1 i) = 0` implies `Z.testbit x i = false`
- `Z.land x (Z.shiftl 1 i) <> 0` implies `Z.testbit x i = true`
- `((x >> k) & 1) = 0` implies `Z.testbit x k = false`
- the converse bridge from `Z.testbit x k = false` back to `((x >> k) & 1) = 0`
- zero reconstruction for a nonnegative 32-bit value whose bits `0..31` are all clear

Key Coq fragment:

```coq
unfold xizi_bitmap_highest_prio_spec.
right.
split.
- lia.
- split.
  + apply land_shiftl_neq0_testbit_true; lia.
  + intros k Hk.
    apply shiftr_land1_eq0_testbit_false with (k := k); try lia.
    apply H5; lia.
```

Why this worked: The C verification conditions are phrased with `Z.land`, `Z.shiftl`, and `Z.shiftr`, while the imported contract uses `Z.testbit`. Once those conversions were made explicit, the arithmetic and witness preservation goals closed cleanly.

2026-06-03 Final checks

Phenomenon: After proof completion, the workspace still contained Coq compilation intermediates under `coq/generated/`.

Location: `/home/yangfp/CAV/OS/CAV/output/verify_20260603_204428v_xizi_bitmap_highest_prio/coq/generated/`.

Fix action: Removed non-`.v` artifacts from `coq/` and confirmed that `input/xizi_bitmap_highest_prio.{c,v}` still match the preserved `original/` copies exactly. The annotated C differs from the input only by added verification annotations; the executable function body and contract text are unchanged.

Why this worked: It restores the workspace to the cleanup state required by the verify runner while preserving the latest generated `.v` sources.

Final Result: Success
