# fb_array_second_rise_value

## Problem

Return the FormalBench scan value that tracks the previous minimum before a later larger value.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `GetGcd.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArraySecondRiseValue {
    public static int fb_array_second_rise_value(int[] arr, int n) {
        int result = 0, min = arr[0];
        for (int i = 1; i < n; i++) { if (arr[i] > min) result = result > min ? result : min; else min = arr[i]; }
        return result;
    }
}
```
