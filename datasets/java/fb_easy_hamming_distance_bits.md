# fb_easy_hamming_distance_bits

## Problem

Return the number of bit positions where nonnegative integers `n1` and `n2` differ.

## Requirements

- `0 <= n1, n2 <= 1000000`.
- Compare binary representations until both numbers become zero.

## Source

- Source: FormalBenchHF base program `HammingDistance.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyHammingDistanceBits {
    public static int fb_easy_hamming_distance_bits(int n1, int n2) {
        int count = 0;
        while (n1 != 0 || n2 != 0) { if ((n1 & 1) != (n2 & 1)) count++; n1 >>= 1; n2 >>= 1; }
        return count;
    }
}
```
