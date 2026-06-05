# LC Lemonade Change Bool CSV

## Problem

Return true if correct change can be given for every customer.

## Requirements

- `bills` is a comma-separated list of `5`, `10`, or `20`.

## Source

- Source: LeetCode problem `lemonade-change`.
- URL: https://leetcode.com/problems/lemonade-change/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_lemonade_change_bool_csv(const char *bills) {
    int five = 0, ten = 0, i = 0;
    while (bills[i] != '\0') { int v = 0; while (bills[i] >= '0' && bills[i] <= '9') { v = v * 10 + (bills[i] - '0'); i++; } if (v == 5) five++; else if (v == 10) { if (five == 0) return 0; five--; ten++; } else { if (ten > 0 && five > 0) { ten--; five--; } else if (five >= 3) five -= 3; else return 0; } if (bills[i] == ',') i++; }
    return 1;
}
```
