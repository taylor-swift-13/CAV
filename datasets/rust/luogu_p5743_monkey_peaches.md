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

```rust
pub fn luogu_p5743_monkey_peaches(n: i32) -> i32 {
    let mut peaches = 1; let mut day = 1; while day < n { peaches = (peaches + 1) * 2; day += 1; } peaches
}
```
