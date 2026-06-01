# SpecGenBench Unique Num First Index

## Problem

Return the first index whose value appears exactly once in the first `n` elements; return `-1` if no such value exists.

## Requirements

- `n >= 0` and `arr` has at least `n` elements.
- Use nested scan order.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/UniqueNumNested`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/UniqueNumNested/UniqueNumNested.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class SgUniqueNumFirstIndex {
    public static int sg_unique_num_first_index(int n, int[] arr) {
        for (int i = 0; i < n; i++) {
            boolean found = false;
            for (int j = 0; j < n; j++) if (i != j && arr[i] == arr[j]) found = true;
            if (!found) return i;
        }
        return -1;
    }
}
```
