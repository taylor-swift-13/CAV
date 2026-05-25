# fb_jacobsthal_number

## Problem

Return the `n`th Jacobsthal number with `J(0)=0`, `J(1)=1`, and `J(n)=J(n-1)+2*J(n-2)`.

## Requirements

- `1 <= n <= 30`.
- Return the signed 32-bit integer result.

## Source

- Source: FormalBenchHF base program `JacobsthalNum.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbJacobsthalNumber {
    public static int fb_jacobsthal_number(int n) {
        int[] values = new int[n + 1];
        values[0] = 0; values[1] = 1;
        for (int i = 2; i <= n; i++) values[i] = values[i - 1] + 2 * values[i - 2];
        return values[n];
    }
}
```
