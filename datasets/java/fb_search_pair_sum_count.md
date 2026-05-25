# fb_search_pair_sum_count

## Problem

Return how many unordered pairs in the first `n` elements of `arr` sum to `target`.

## Requirements

- `0 <= n <= arr.length <= 50`.
- Array values are signed 32-bit integers.

## Source

- Source: FormalBenchHF base program `GetPairsCount.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchPairSumCount {
    public static int fb_search_pair_sum_count(int[] arr, int n, int target) {
        int count = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] + arr[j] == target) count++;
        return count;
    }
}
```
