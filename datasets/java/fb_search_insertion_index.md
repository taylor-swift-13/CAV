# fb_search_insertion_index

## Problem

Return the index of `x` in sorted `a` if present; otherwise return the left insertion index.

## Requirements

- `0 <= n <= a.length <= 50`.
- The first `n` elements are sorted.

## Source

- Source: FormalBenchHF base program `LeftInsertion.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchInsertionIndex {
    public static int fb_search_insertion_index(int[] a, int n, int x) {
        int left = 0, right = n - 1;
        while (left <= right) { int mid = (left + right) / 2; if (a[mid] == x) return mid; else if (a[mid] < x) left = mid + 1; else right = mid - 1; }
        return left;
    }
}
```
