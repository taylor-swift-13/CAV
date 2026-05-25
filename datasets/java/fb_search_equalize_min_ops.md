# fb_search_equalize_min_ops

## Problem

Return the number of `k`-sized increments needed to raise all first `n` array elements to the maximum value, or `-1` if impossible.

## Requirements

- `1 <= n <= arr.length <= 50`.
- `k > 0`.

## Source

- Source: FormalBenchHF base program `MinOps.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchEqualizeMinOps {
    public static int fb_search_equalize_min_ops(int[] arr, int n, int k) {
        int max = arr[0]; for (int i = 1; i < n; i++) if (arr[i] > max) max = arr[i];
        int res = 0; for (int i = 0; i < n; i++) { if ((max - arr[i]) % k != 0) return -1; res += (max - arr[i]) / k; }
        return res;
    }
}
```
