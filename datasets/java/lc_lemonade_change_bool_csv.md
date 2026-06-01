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

```java
class LcLemonadeChangeBoolCsv {
    public static boolean lc_lemonade_change_bool_csv(String bills) {
        int five = 0, ten = 0; for (String part : bills.split(",")) { int v = Integer.parseInt(part); if (v == 5) five++; else if (v == 10) { if (five == 0) return false; five--; ten++; } else { if (ten > 0 && five > 0) { ten--; five--; } else if (five >= 3) five -= 3; else return false; } } return true;
    }
}
```
