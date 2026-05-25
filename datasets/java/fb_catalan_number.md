# fb_catalan_number

## Problem

Return the `num`th Catalan number using the standard dynamic programming recurrence.

## Requirements

- `0 <= num <= 12`.
- Use `C[0]=1` and `C[i]=sum(C[j]*C[i-j-1])` for `0 <= j < i`.

## Source

- Source: FormalBenchHF base program `CatalanNumber.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbCatalanNumber {
    public static int fb_catalan_number(int num) {
        int[] catalan = new int[num + 1];
        catalan[0] = 1;
        for (int i = 1; i <= num; i++) {
            for (int j = 0; j < i; j++) catalan[i] += catalan[j] * catalan[i - j - 1];
        }
        return catalan[num];
    }
}
```
