# balanced_string_split_count

## Problem

Return the maximum number of balanced substrings in a string containing only `L` and `R`.

## Requirements

- Input contains only `L` and `R`.
- The full input is balanced.
- A balanced substring has the same number of `L` and `R` characters.
- Return the maximum count obtained by greedy left-to-right splitting.

## Source

- Source: LeetCode problem `split-a-string-in-balanced-strings`.
- URL: https://leetcode.com/problems/split-a-string-in-balanced-strings/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class BalancedStringSplitCount {
    public static int balanced_string_split_count(String s) {
        int balance = 0, count = 0;
        for (int i = 0; i < s.length(); i++) { if (s.charAt(i) == 'L') balance++; else balance--; if (balance == 0) count++; }
        return count;
    }
}
```
