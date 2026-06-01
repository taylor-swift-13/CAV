# SpecGenBench Ugly Number Flag

## Problem

Return true if `n` is positive and has no prime factors except `2`, `3`, and `5`.

## Requirements

- `n` is a signed 32-bit integer.
- Return false for `n <= 0`.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/UglyNum`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/UglyNum/UglyNum.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SgUglyNumberFlag {
    public static boolean sg_ugly_number_flag(int n) {
        if (n <= 0) return false;
        int[] factors = {2, 3, 5};
        for (int i = 0; i < factors.length; i++) while (n % factors[i] == 0) n /= factors[i];
        return n == 1;
    }
}
```
