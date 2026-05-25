# fb_search_odd_then_even_number

## Problem

List numbers `1..n` with odds first and evens second; return the `k`th listed number, or `0` if `k` is out of range.

## Requirements

- `1 <= n <= 10000`.
- `1 <= k <= 10000`.

## Source

- Source: FormalBenchHF base program `GetNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbSearchOddThenEvenNumber {
    public static int fb_search_odd_then_even_number(int n, int k) {
        int count = 0;
        for (int i = 1; i <= n; i += 2) { count++; if (count == k) return i; }
        for (int i = 2; i <= n; i += 2) { count++; if (count == k) return i; }
        return 0;
    }
}
```
