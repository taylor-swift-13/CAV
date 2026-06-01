# FormalBench Count Nondecreasing Pairs

## Problem

Return how many unordered index pairs `i < j` in the first `n` elements satisfy `a[i] <= a[j]`.

## Requirements

- `n >= 0` and `a` has at least `n` elements.
- Count each pair once.
- The result fits in a signed 32-bit integer.

## Source

- Source: FormalBench problem `FormalBenchHF/base/programs/CountPairs.java`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: local rewrite from SESpec java_flat.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbExtCountNondecreasingPairs {
    public static int fb_ext_count_nondecreasing_pairs(int n, int[] a) {
        int count = 0;
        for (int i = 0; i < n; i++) {
            for (int j = i + 1; j < n; j++) if (a[i] <= a[j]) count++;
        }
        return count;
    }
}
```
