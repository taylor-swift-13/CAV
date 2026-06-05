# count_asterisks_between_bars

## Problem

Count `*` characters that are not between a pair of vertical bars.

## Requirements

- Bars occur in pairs.
- Characters between the first and second bar of each pair are ignored.
- Count only `*` characters outside ignored ranges.
- Other characters do not affect the count.

## Source

- Source: LeetCode problem `count-asterisks`.
- URL: https://leetcode.com/problems/count-asterisks/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int count_asterisks_between_bars(const char *s) {
    int inside = 0;
    int count = 0;
    for (int i = 0; s[i] != '\0'; i++) {
        if (s[i] == '|') inside = !inside;
        else if (s[i] == '*' && !inside) count++;
    }
    return count;
}
```
