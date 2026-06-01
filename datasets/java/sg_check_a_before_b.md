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

```java
class SgCheckABeforeB {
    public static boolean sg_check_a_before_b(String s) {
        boolean seenB = false;
        for (int i = 0; i < s.length(); i++) {
            if (s.charAt(i) == 'b') seenB = true;
            if (s.charAt(i) == 'a' && seenB) return false;
        }
        return true;
    }
}
```
