# Luogu P1421 Pencil Count

## Problem

Given a budget in yuan and jiao, return how many 1.9-yuan pencils can be bought.

## Requirements

- `yuan >= 0` and `0 <= jiao < 10`.
- One pencil costs exactly `19` jiao.
- Use integer division and ignore leftover money.

## Source

- Source: Luogu problem `P1421`.
- URL: https://www.luogu.com.cn/problem/P1421
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP1421PencilCount {
    public static int luogu_p1421_pencil_count(int yuan, int jiao) {
        return (yuan * 10 + jiao) / 19;
    }
}
```
