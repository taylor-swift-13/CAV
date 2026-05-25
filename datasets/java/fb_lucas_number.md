# fb_lucas_number

## Problem

Return the `n`th Lucas number with `L(0)=2`, `L(1)=1`, and `L(n)=L(n-1)+L(n-2)`.

## Requirements

- `1 <= n <= 30`.
- Return the signed 32-bit integer result.

## Source

- Source: FormalBenchHF base program `FindLucas.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbLucasNumber {
    public static int fb_lucas_number(int n) {
        int[] values = new int[n + 1];
        values[0] = 2; values[1] = 1;
        for (int i = 2; i <= n; i++) values[i] = values[i - 1] + values[i - 2];
        return values[n];
    }
}
```
