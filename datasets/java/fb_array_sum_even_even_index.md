# fb_array_sum_even_even_index

## Problem

Return the sum of elements that are both at an even index and even-valued in the first `n` elements.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `SumEvenAndEvenIndex.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArraySumEvenEvenIndex {
    public static int fb_array_sum_even_even_index(int[] arr, int n) {
        int sum = 0;
        for (int i = 0; i < n; i++) if (i % 2 == 0 && arr[i] % 2 == 0) sum += arr[i];
        return sum;
    }
}
```
