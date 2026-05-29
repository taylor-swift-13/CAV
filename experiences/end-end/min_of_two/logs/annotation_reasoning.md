# Annotation Reasoning

## Required pre-edit experience search

- Read `/home/yangfp/CAV-JAVA/experiences/INDEX.md`.
- Read required general references:
  - `/home/yangfp/CAV-JAVA/experiences/general/INV/README.md`
  - `/home/yangfp/CAV-JAVA/experiences/general/ASSERTION/README.md`
  - `/home/yangfp/CAV-JAVA/experiences/general/LEMMA/README.md`
  - `/home/yangfp/CAV-JAVA/experiences/general/ANTI_CHEATING.md`
  - `/home/yangfp/CAV-JAVA/experiences/general/OPENJML/README.md`
- Searched `/home/yangfp/CAV-JAVA/experiences/end-end` with:
  - `find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 4 -type f | sort`
  - `rg -n "return_min|return_max|branch_on_order|algorithm_family.*selection|semantic_intent|case_split|Math.min|min\(|<=|>=|ensures.*result" /home/yangfp/CAV-JAVA/experiences/end-end`
- Relevant completed example path: `/home/yangfp/CAV-JAVA/experiences/end-end/max_of_two`.
- Reason it is relevant: the max-of-two example uses the same scalar-only, read-only, single-branch selection pattern with `assignable \nothing` and branch-conditioned postconditions. This min-of-two task reverses the selected order relation but keeps the same direct case-split proof shape.

## Baseline verification

- Command: `scripts/check_jml_cheating.py --baseline /home/yangfp/CAV-JAVA/output/verify_20260423_044109_min_of_two/original/min_of_two.java /home/yangfp/CAV-JAVA/output/verify_20260423_044109_min_of_two/verified/min_of_two.java`
- Result: passed.
- Command: `scripts/run_openjml_verify.sh /home/yangfp/CAV-JAVA/output/verify_20260423_044109_min_of_two/verified/min_of_two.java`
- Result: passed.

## Annotation decision

No Java annotation edits were needed. The original and verified files already contain the necessary baseline contract:

```java
//@ requires true;
//@ assignable \nothing;
//@ ensures a <= b ==> \result == a;
//@ ensures a > b ==> \result == b;
//@ ensures \result <= a && \result <= b;
//@ ensures \result == a || \result == b;
```

The `if (a <= b)` branch directly proves the `a` result case, including the lower-bound and returned-input postconditions. The fall-through path has `a > b`, returns `b`, and proves the remaining min lower-bound and returned-input postconditions. The method has no heap effects and needs no loop invariants, helper lemmas, assertions, or extra range preconditions.

## General experience update

No update under `/home/yangfp/CAV-JAVA/experiences/general` was needed. This run reused the existing scalar branch-split selection pattern from `/home/yangfp/CAV-JAVA/experiences/end-end/max_of_two` and did not produce a new reusable OpenJML lesson.
