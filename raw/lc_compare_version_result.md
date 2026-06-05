# LC Compare Version Result

## Problem

Compare two version strings and return `-1`, `0`, or `1`.

## Requirements

- Version revisions are dot-separated nonnegative integers.
- Leading zeroes are ignored.

## Source

- Source: LeetCode problem `compare-version-numbers`.
- URL: https://leetcode.com/problems/compare-version-numbers/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_compare_version_result(const char *version1, const char *version2) {
    int i = 0, j = 0; while (version1[i] != '\0' || version2[j] != '\0') { long long a = 0, b = 0; while (version1[i] >= '0' && version1[i] <= '9') { a = a * 10 + (version1[i] - '0'); i++; } while (version2[j] >= '0' && version2[j] <= '9') { b = b * 10 + (version2[j] - '0'); j++; } if (a < b) return -1; if (a > b) return 1; if (version1[i] == '.') i++; if (version2[j] == '.') j++; } return 0;
}
```
