# fb_array_first_even

## Problem

Return the first even value in the first `n` elements of `nums`, or `0` if no even value appears.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FirstEven.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayFirstEven {
    public static int fb_array_first_even(int[] nums, int n) {
        int even = 0;
        for (int i = 0; i < n; i++) if (nums[i] % 2 == 0) { even = nums[i]; break; }
        return even;
    }
}
```
