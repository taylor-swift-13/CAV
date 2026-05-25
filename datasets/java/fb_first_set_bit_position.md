# fb_first_set_bit_position

## Problem

Return the one-based position of the least significant set bit in `n`.

## Requirements

- `1 <= n <= 1000000`.
- The least significant bit has position `1`.

## Source

- Source: FormalBenchHF base program `GetFirstSetBitPos.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbFirstSetBitPosition {
    public static int fb_first_set_bit_position(int n) {
        int i = 1;
        while ((n & 1) == 0) { n >>= 1; i++; }
        return i;
    }
}
```
