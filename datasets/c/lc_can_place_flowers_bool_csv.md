# LC Can Place Flowers Bool CSV

## Problem

Return true if `n` new flowers can be planted without adjacent flowers.

## Requirements

- `bed` is a comma-separated list of `0` and `1`.
- Existing flowers are not adjacent.

## Source

- Source: LeetCode problem `can-place-flowers`.
- URL: https://leetcode.com/problems/can-place-flowers/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_can_place_flowers_bool_csv(const char *bed, int n) {
    int a[256], len = 0, i = 0; while (bed[i] != '\0') { a[len++] = bed[i] - '0'; i++; if (bed[i] == ',') i++; }
    for (int j = 0; j < len && n > 0; j++) if (a[j] == 0 && (j == 0 || a[j - 1] == 0) && (j == len - 1 || a[j + 1] == 0)) { a[j] = 1; n--; }
    return n <= 0;
}
```
