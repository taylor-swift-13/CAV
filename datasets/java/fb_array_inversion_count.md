# fb_array_inversion_count

## Problem

Return the number of inversions in the first `n` elements of `arr`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `GetInvCount.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayInversionCount {
    public static int fb_array_inversion_count(int[] arr, int n) {
        int count = 0;
        for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (arr[i] > arr[j]) count++;
        return count;
    }
}
```
