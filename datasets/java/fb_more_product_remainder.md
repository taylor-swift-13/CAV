# fb_more_product_remainder

## Problem

Return the product of the first `lens` elements of `arr`, modulo `n`.

## Requirements

- Array length is at most `20`.
- `1 <= n <= 100000`.
- The product fits in signed 64-bit integer for the stated tests.

## Source

- Source: FormalBenchHF base program `FindRemainder.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreProductRemainder {
    public static int fb_more_product_remainder(int[] arr, int lens, int n) {
        long product = 1;
        for (int i = 0; i < lens; i++) product *= arr[i];
        return (int)(product % n);
    }
}
```
