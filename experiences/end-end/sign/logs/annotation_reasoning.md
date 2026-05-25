# Annotation Reasoning

## Required reference search

- Read `/home/yangfp/CAV-JAVA/experiences/INDEX.md` and the required general notes: `INV.md`, `ASSERTION.md`, `LEMMA.md`, `ANTI_CHEATING.md`, and `OPENJML.md`.
- Searched completed examples with:
  - `find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 4 -type f | sort`
  - `rg -n "case_split|control_flow|if|ensures|Final Result|Postcondition|workspace_fingerprint" /home/yangfp/CAV-JAVA/experiences/end-end`
- Relevant completed examples:
  - `/home/yangfp/CAV-JAVA/experiences/end-end/clamp_nonnegative`
  - `/home/yangfp/CAV-JAVA/experiences/end-end/abs`
  - `/home/yangfp/CAV-JAVA/experiences/end-end/max_of_two`
- Reason they are relevant: these examples use scalar `if` control flow, `assignable \nothing`, direct case-split postcondition proofs, and no heap mutation. `sign` has the same proof shape with three return literals instead of returning an input or one of two inputs.

## Baseline verification

- Command: `scripts/check_jml_cheating.py --baseline /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/original/sign.java /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/verified/sign.java`
- Result: passed.
- Command: `scripts/run_openjml_verify.sh /home/yangfp/CAV-JAVA/output/verify_20260423_044724_sign/verified/sign.java`
- Result: passed.

## Annotation decision

No Java annotation edits were needed. The original and verified files already contain the necessary baseline contract:

```java
//@ requires true;
//@ assignable \nothing;
//@ ensures x > 0 ==> \result == 1;
//@ ensures x == 0 ==> \result == 0;
//@ ensures x < 0 ==> \result == -1;
//@ ensures \result == -1 || \result == 0 || \result == 1;
```

The first branch has path condition `x > 0` and returns `1`, directly proving the positive-input postcondition and the result-range postcondition. The second branch is reached with `x <= 0`; its condition `x == 0` returns `0`, proving the zero-input postcondition and range. The final return is reached with `x <= 0 && x != 0`, which implies `x < 0`, and returns `-1`, proving the negative-input postcondition and range. The method has no heap effects and needs no loop invariants, helper lemmas, assertions, or extra range preconditions.

## General experience update

No update under `/home/yangfp/CAV-JAVA/experiences/general` was needed. This run reused the already documented scalar case-split and anti-cheating patterns without introducing a new reusable OpenJML lesson.
