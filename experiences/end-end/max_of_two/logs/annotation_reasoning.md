# Annotation Reasoning

## Required pre-edit experience search

- Read `/home/yangfp/CAV-JAVA/experiences/INDEX.md`.
- Searched `/home/yangfp/CAV-JAVA/experiences/end-end` with:
  - `find /home/yangfp/CAV-JAVA/experiences/end-end -maxdepth 4 -type f | sort`
  - `rg -n "return_max|selection|case_split|if|ensures|Final Result|workspace_fingerprint" /home/yangfp/CAV-JAVA/experiences/end-end`
- Relevant completed example path: `/home/yangfp/CAV-JAVA/experiences/end-end/abs`.
- Reason it is relevant: the ABS example uses a scalar `if` branch, `assignable \nothing`, and direct case-split postcondition proof. This max-of-two task has the same proof shape but selects the larger of two inputs rather than the absolute value of one input.

## Baseline verification

- Command: `scripts/check_jml_cheating.py --baseline /home/yangfp/CAV-JAVA/output/verify_20260423_043757_max_of_two/original/max_of_two.java /home/yangfp/CAV-JAVA/output/verify_20260423_043757_max_of_two/verified/max_of_two.java`
- Result: passed.
- Command: `scripts/run_openjml_verify.sh /home/yangfp/CAV-JAVA/output/verify_20260423_043757_max_of_two/verified/max_of_two.java`
- Result: passed.

## Annotation decision

No Java annotation edits were needed. The original and verified files already contain the necessary baseline contract:

```java
//@ requires true;
//@ assignable \nothing;
//@ ensures a >= b ==> \result == a;
//@ ensures a < b ==> \result == b;
//@ ensures \result >= a && \result >= b;
//@ ensures \result == a || \result == b;
```

The `if (a >= b)` branch directly proves the `a` result case, including equality. The fall-through path has `a < b`, returns `b`, and proves both max lower-bound and returned-input postconditions. The method has no heap effects and needs no loop invariants, helper lemmas, assertions, or extra range preconditions.

## General experience update

No update under `/home/yangfp/CAV-JAVA/experiences/general` was needed. This run reused the existing scalar branch-split selection pattern from `/home/yangfp/CAV-JAVA/experiences/end-end/abs` and did not produce a new reusable OpenJML lesson.
