# fb_array_distinct_pair_count

## Problem

Return how many unordered pairs contain two different values.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `CountPairs.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayDistinctPairCount {
    public static int fb_array_distinct_pair_count(int[] arr, int n) {
        int count = 0;
        for (int i = 0; i < n - 1; i++) for (int j = i + 1; j < n; j++) if (arr[i] != arr[j]) count++;
        return count;
    }
}
```
