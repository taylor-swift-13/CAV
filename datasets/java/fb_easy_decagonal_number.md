# fb_easy_decagonal_number

## Problem

Return the `n`th value of the FormalBench decagonal-number recurrence.

## Requirements

- `0 <= n <= 1000`.
- Use `f[0]=0` and `f[i+1]=f[i]+8*i+1`.

## Source

- Source: FormalBenchHF base program `IsNumDecagonal.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbEasyDecagonalNumber {
    public static int fb_easy_decagonal_number(int n) {
        int value = 0;
        for (int i = 0; i <= n - 1; i++) value += 8 * i + 1;
        return value;
    }
}
```
