# max_consecutive_ones_csv

## Problem

Return the longest run of `1` values in comma-separated binary string `bits`.

## Requirements

- `bits` is comma-separated `0` and `1` characters with no spaces.
- The empty string represents an empty array.
- Return the maximum number of adjacent ones.
- Commas are separators and are ignored by the run count.

## Source

- Source: LeetCode problem `max-consecutive-ones`.
- URL: https://leetcode.com/problems/max-consecutive-ones/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int max_consecutive_ones_csv(const char *bits) {
    int best = 0;
    int cur = 0;
    for (int i = 0; bits[i] != '\0'; i++) {
        if (bits[i] == '1') { cur++; if (cur > best) best = cur; }
        else if (bits[i] == '0') cur = 0;
    }
    return best;
}
```
