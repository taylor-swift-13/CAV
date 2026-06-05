# SpecGenBench Check A Before B

## Problem

Return true if every `a` in string `s` appears before every `b`.

## Requirements

- `s` contains only `a` and `b`.
- The empty string is allowed.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/CheckABeforeB`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/CheckABeforeB/CheckABeforeB.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_check_a_before_b(const char *s) {
    int seen_b = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        if (s[i] == 'b') seen_b = 1;
        if (s[i] == 'a' && seen_b) return 0;
    }
    return 1;
}
```
