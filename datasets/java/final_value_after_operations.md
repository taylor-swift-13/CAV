# final_value_after_operations

## Problem

Starting from zero, apply comma-separated operations `++X`, `X++`, `--X`, or `X--` and return the final value.

## Requirements

- `operations` is comma-separated with no spaces.
- Allowed operations are `++X`, `X++`, `--X`, and `X--`.
- Increment operations add one; decrement operations subtract one.
- The empty string represents no operations.

## Source

- Source: LeetCode problem `final-value-of-variable-after-performing-operations`.
- URL: https://leetcode.com/problems/final-value-of-variable-after-performing-operations/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class FinalValueAfterOperations {
    public static int final_value_after_operations(String operations) {
        if (operations.isEmpty()) return 0;
        int value = 0;
        for (String op : operations.split(",")) { if (op.charAt(0) == '+' || op.charAt(1) == '+') value++; else value--; }
        return value;
    }
}
```
