# fb_array_subarray_product_sum

## Problem

Return the sum of products of every contiguous subarray in the first `n` elements.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `SumOfSubarrayProd.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_array_subarray_product_sum(int arr[], int n) {
    int sum = 0;
    for (int i = 0; i < n; i++) { int product = 1; for (int j = i; j < n; j++) { product *= arr[j]; sum += product; } }
    return sum;
}
```
