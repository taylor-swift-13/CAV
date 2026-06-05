## Round 1

- Phenomenon: `symexec` stopped at `/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c:15` with `Error: Lack of assertions in some paths for the loop!`.
- Location: outer `while (num >= 10)` and inner `while (num > 0)` in [verify_20260604_162058_add_digits.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c:13).
- Repair action: add one invariant per loop instead of changing the contract. The outer invariant will preserve `0 <= num` and `digital_root_z(num) == digital_root_z(num@pre)`. The inner invariant will existentially freeze the outer-round starting value `n0` and preserve `sum + digit_sum_z(num) == digit_sum_z(n0)` together with `0 <= num`, `0 <= sum`, and the same digital-root link to `num@pre`.
- Key annotation shape:
  - outer loop: `0 <= num && digital_root_z(num) == digital_root_z(num@pre)`
  - inner loop: `exists n0, 0 <= n0 && digital_root_z(n0) == digital_root_z(num@pre) && sum + digit_sum_z(num) == digit_sum_z(n0) && 0 <= num && 0 <= sum`
- Why this shape: the inner loop is a decimal scan, so the natural preserved quantity is “processed digit sum + remaining digit sum = total digit sum of the outer-round input”. When the inner loop exits, `num == 0` makes `sum == digit_sum_z(n0)`. After `num = sum`, the outer loop only needs the mathematical fact that one digit-sum step preserves the final digital root.

## Round 2

- Phenomenon: generated `/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v` left `add_digits_safety_wit_4` with target `(sum + num % 10) <= INT_MAX`, but the inner invariant only said `0 <= n0` and lost every upper-bound fact about the frozen outer-round input.
- Location: `add_digits_safety_wit_4` in [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:60) traces back to the inner loop invariant in [verify_20260604_162058_add_digits.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c:20).
- Repair action: strengthen both loop invariants with explicit `<= INT_MAX` facts for the live scalar state and the existential `n0`. This keeps the VC in arithmetic form and avoids depending on hidden local-store facts for an existential witness.
- Key annotation change:
  - outer loop adds `num <= INT_MAX`
  - inner loop adds `n0 <= INT_MAX`, `num <= INT_MAX`, and `sum <= INT_MAX`
- Why this change: the executable C state is all `int`, so these bounds are semantically true and cheap to preserve. Carrying them in the invariant gives the safety witness a direct path to bounded addition instead of reconstructing representation bounds indirectly from local permissions.

## Round 3

- Phenomenon: `coq/generated/add_digits_goal.v` still generated `add_digits_entail_wit_1` as a false pure entry theorem `0 <= num_pre |- num_pre <= INT_MAX`.
- Location: [add_digits_goal.v](/home/yangfp/CAV/C/CAV/output/verify_20260604_162058_add_digits/coq/generated/add_digits_goal.v:156) originates from initializing the strengthened outer invariant in [verify_20260604_162058_add_digits.c](/home/yangfp/CAV/C/CAV/annotated/verify_20260604_162058_add_digits.c:13).
- Repair action: add `/*@ num <= INT_MAX by local */` immediately before the outer loop so the generated witness keeps the typed local-store fact instead of requiring a false pure arithmetic premise from the contract.
- Key annotation change:
  - bridge assertion before the outer `while`: `num <= INT_MAX by local`
- Why this change: `num` is a C `int` parameter, so its machine-range fact is available from the local store at function entry. Using `by local` keeps the verification within Verify’s allowed annotation layer and avoids unsound proof attempts for a proposition the contract never stated.
