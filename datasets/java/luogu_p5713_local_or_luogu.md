# Luogu P5713 Local Or Luogu

## Problem

Compare `5*x` with `11+3*x`; return `1` when Local is cheaper, otherwise `2` for Luogu.

## Requirements

- `x >= 0`.
- This numeric code preserves the original two-way output decision.

## Source

- Source: Luogu problem `P5713`.
- URL: https://www.luogu.com.cn/problem/P5713
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5713LocalOrLuogu {
    public static int luogu_p5713_local_or_luogu(int x) {
        return 5 * x < 11 + 3 * x ? 1 : 2;
    }
}
```
