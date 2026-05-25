# fb_more_smallest_missing_index

## Problem

Given a sorted array segment where values may equal their indices, return the first index in `[left, right+1]` whose value is missing from its matching index.

## Requirements

- Array length is at most `50`.
- `0 <= left <= right < array length`.

## Source

- Source: FormalBenchHF base program `SmallestMissing.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbMoreSmallestMissingIndex {
    public static int fb_more_smallest_missing_index(int[] a, int left, int right) {
        int i = left, j = right;
        while (i <= j) { int mid = (i + j) / 2; if (a[mid] == mid) i = mid + 1; else j = mid - 1; }
        return i;
    }
}
```
