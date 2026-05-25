# fb_array_fixed_point

## Problem

For a sorted array, return an index `i` such that `arr[i] == i`, or `-1` if none exists.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `FindFixedPoint.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayFixedPoint {
    public static int fb_array_fixed_point(int[] arr, int n) {
        int start = 0, end = n - 1;
        while (start <= end) { int mid = start + (end - start) / 2; if (arr[mid] == mid) return mid; else if (arr[mid] < mid) start = mid + 1; else end = mid - 1; }
        return -1;
    }
}
```
