# SpecGenBench Repeated Char First Index

## Problem

Return the first index `i` whose character appears again later in lowercase string `s`; return `-1` if no character repeats.

## Requirements

- `s` contains lowercase English letters only.
- The empty string is allowed.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/RepeatedCharNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/RepeatedCharNested/RepeatedCharNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SgRepeatedCharFirstIndex {
    public static int sg_repeated_char_first_index(String s) {
        for (int i = 0; i < s.length(); i++) for (int j = i + 1; j < s.length(); j++) if (s.charAt(i) == s.charAt(j)) return i;
        return -1;
    }
}
```
