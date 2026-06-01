# LC Min Stack Final Min CSV

## Problem

Simulate stack operations and return the minimum value after all operations.

## Requirements

- Operations are semicolon-separated: `push:x` or `pop`.
- The final stack is nonempty.
- Pop operations are valid.

## Source

- Source: LeetCode problem `min-stack`.
- URL: https://leetcode.com/problems/min-stack/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinStackFinalMinCsv {
    public static int lc_min_stack_final_min_csv(String ops) {
        int[] st = new int[128]; int top = 0;
        for (String op : ops.split(";")) { if (op.startsWith("push:")) st[top++] = Integer.parseInt(op.substring(5)); else top--; }
        int min = st[0]; for (int i = 1; i < top; i++) if (st[i] < min) min = st[i];
        return min;
    }
}
```
