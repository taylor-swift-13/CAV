# SpecGenBench All Unique Lowercase

## Problem

Return true if lowercase string `s` contains no repeated character.

## Requirements

- `s` contains lowercase English letters only.
- Strings longer than `26` must return false.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsAllUnique`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsAllUnique/IsAllUnique.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_all_unique_lowercase(const char *s) {
    int seen = 0;
    int len = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        len++;
        if (len > 26) return 0;
        int bit = 1 << (s[i] - 'a');
        if ((seen & bit) != 0) return 0;
        seen |= bit;
    }
    return 1;
}
```
