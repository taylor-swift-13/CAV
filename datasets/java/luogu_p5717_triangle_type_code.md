# Luogu P5717 Triangle Type Code

## Problem

Classify three side lengths.

## Requirements

- Return `0` when the sides cannot form a triangle.
- Return `3` for equilateral, `2` for isosceles non-equilateral, and `1` for scalene.

## Source

- Source: Luogu problem `P5717`.
- URL: https://www.luogu.com.cn/problem/P5717
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP5717TriangleTypeCode {
    public static int luogu_p5717_triangle_type_code(int a, int b, int c) {
        if (a + b <= c || a + c <= b || b + c <= a) return 0;
        if (a == b && b == c) return 3;
        if (a == b || a == c || b == c) return 2;
        return 1;
    }
}
```
