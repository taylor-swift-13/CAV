# fb_easy_toggle_even_bit_positions

## Problem

Toggle every even-indexed bit position that exists in the binary representation of `n`, using zero-based bit positions.

## Requirements

- `1 <= n <= 1000000`.
- Only positions below the highest set bit are considered.

## Source

- Source: FormalBenchHF base program `EvenBitToggleNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyToggleEvenBitPositions {
    public static int fb_easy_toggle_even_bit_positions(int n) {
        int res = 0, count = 0, temp = n;
        while (temp > 0) { if (count % 2 == 0) res |= (1 << count); count++; temp >>= 1; }
        return n ^ res;
    }
}
```
