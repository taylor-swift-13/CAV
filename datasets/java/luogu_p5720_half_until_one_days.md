# Luogu P5720 Half Until One Days

## Problem

Starting with length `n`, repeatedly replace it by half rounded down until it becomes `1`; return the number of values printed including the initial value.

## Requirements

- `n >= 1`.

## Source

- Source: Luogu problem `P5720`.
- URL: https://www.luogu.com.cn/problem/P5720
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5720HalfUntilOneDays {
    public static int luogu_p5720_half_until_one_days(int n) {
        int count = 1;
        while (n > 1) { n /= 2; count++; }
        return count;
    }
}
```
