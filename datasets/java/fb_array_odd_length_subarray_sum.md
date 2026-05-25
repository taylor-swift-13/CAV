# fb_array_odd_length_subarray_sum

## Problem

Return the sum of every odd-length contiguous subarray in the first `n` elements of `arr`.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `OddLengthSum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayOddLengthSubarraySum {
    public static int fb_array_odd_length_subarray_sum(int[] arr, int n) {
        int sum = 0, l = n;
        for (int i = 0; i < l; i++) sum += ((((i + 1) * (l - i) + 1) / 2) * arr[i]);
        return sum;
    }
}
```
