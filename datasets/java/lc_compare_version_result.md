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

```java
class LcCompareVersionResult {
    public static int lc_compare_version_result(String version1, String version2) {
        int i = 0, j = 0; while (i < version1.length() || j < version2.length()) { long a = 0, b = 0; while (i < version1.length() && version1.charAt(i) != '.') a = a * 10 + version1.charAt(i++) - '0'; while (j < version2.length() && version2.charAt(j) != '.') b = b * 10 + version2.charAt(j++) - '0'; if (a < b) return -1; if (a > b) return 1; if (i < version1.length()) i++; if (j < version2.length()) j++; } return 0;
    }
}
```
