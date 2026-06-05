# Luogu P5710 Property Mask

## Problem

Return the four boolean results from Luogu P5710 packed as bits 0..3.

## Requirements

- For input `x`, the predicates are: even and greater than 4; even or greater than 4; exactly one of those; neither.
- Bit `i` is set when predicate `i` is true.

## Source

- Source: Luogu problem `P5710`.
- URL: https://www.luogu.com.cn/problem/P5710
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int luogu_p5710_property_mask(int x) {
    int a = x % 2 == 0, b = x > 4, ans = 0; if (a && b) ans |= 1; if (a || b) ans |= 2; if (a != b) ans |= 4; if (!a && !b) ans |= 8; return ans;
}
```
