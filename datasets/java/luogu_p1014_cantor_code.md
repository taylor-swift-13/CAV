# Luogu P1014 Cantor Code

## Problem

Return the Cantor-table fraction at position `n` encoded as `numerator * 1000 + denominator`.

## Requirements

- Use the zigzag diagonal order from Luogu P1014.
- `n` is positive.

## Source

- Source: Luogu problem `P1014`.
- URL: https://www.luogu.com.cn/problem/P1014
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1014CantorCode {
    public static int luogu_p1014_cantor_code(int n) {
        int diag = 1, used = 0; while (used + diag < n) { used += diag; diag++; } int offset = n - used; int num, den; if (diag % 2 == 0) { num = offset; den = diag - offset + 1; } else { num = diag - offset + 1; den = offset; } return num * 1000 + den;
    }
}
```
