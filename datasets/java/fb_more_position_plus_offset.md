# fb_more_position_plus_offset

## Problem

Return the first index of `value` in the first `n` elements of `a`, plus `offset`; use index `0` if the value is not found.

## Requirements

- Array length is at most `50`.
- Use zero-based indexing.

## Source

- Source: FormalBenchHF base program `GetPosition.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMorePositionPlusOffset {
    public static int fb_more_position_plus_offset(int[] a, int n, int value, int offset) {
        int pos = 0;
        for (int i = 0; i < n; i++) { if (a[i] == value) { pos = i; break; } }
        return pos + offset;
    }
}
```
