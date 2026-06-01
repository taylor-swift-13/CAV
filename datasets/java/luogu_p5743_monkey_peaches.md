# Luogu P5743 Monkey Peaches

## Problem

Return the initial number of peaches if after `n` days of eating half plus one each day, one peach remains.

## Requirements

- `n >= 1`.
- Work backward from the final remaining peach.

## Source

- Source: Luogu problem `P5743`.
- URL: https://www.luogu.com.cn/problem/P5743
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5743MonkeyPeaches {
    public static int luogu_p5743_monkey_peaches(int n) {
        int peaches = 1; for (int day = 1; day < n; day++) peaches = (peaches + 1) * 2; return peaches;
    }
}
```
