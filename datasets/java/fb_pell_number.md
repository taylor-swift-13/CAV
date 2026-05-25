# fb_pell_number

## Problem

Return the `n`th Pell number modulo `1000000000`, with `P(0)=0`, `P(1)=1`, and `P(n)=2*P(n-1)+P(n-2)`.

## Requirements

- `1 <= n <= 30`.
- Apply the modulo at each recurrence step.

## Source

- Source: FormalBenchHF base program `GetPell.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FbPellNumber {
    public static int fb_pell_number(int n) {
        int[] values = new int[n + 1];
        values[0] = 0; values[1] = 1;
        for (int i = 2; i <= n; i++) values[i] = (2 * values[i - 1] + values[i - 2]) % 1000000000;
        return values[n];
    }
}
```
