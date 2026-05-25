# fb_array_odd_occurrence_scan

## Problem

Scan the first `n` elements and return the odd value seen at each odd-numbered odd occurrence.

## Requirements

- Array length is at most `50`.
- Array values are signed 32-bit integers.
- Do not read stdin or write stdout.

## Source

- Source: FormalBenchHF base program `GetOddOccurrence.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbArrayOddOccurrenceScan {
    public static int fb_array_odd_occurrence_scan(int[] arr, int n) {
        int result = 0, count = 0;
        for (int i = 0; i < n; i++) if (arr[i] % 2 != 0) { count++; if (count % 2 != 0) result = arr[i]; }
        return result;
    }
}
```
