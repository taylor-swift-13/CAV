# fb_search_first_occurrence

## Problem

Return the first index of `x` in the sorted first `n` elements of `a`, or `-1` if absent.

## Requirements

- `0 <= n <= a.length <= 50`.
- The first `n` elements are sorted in nondecreasing order.

## Source

- Source: FormalBenchHF base program `FindFirstOccurrence.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int fb_search_first_occurrence(int a[], int n, int x) {
    int low = 0, high = n - 1, result = -1;
    while (low <= high) { int mid = (low + high) / 2; if (a[mid] == x) { result = mid; high = mid - 1; } else if (a[mid] < x) low = mid + 1; else high = mid - 1; }
    return result;
}
```
