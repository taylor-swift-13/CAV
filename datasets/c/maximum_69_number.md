# maximum_69_number

## Problem

Given a positive decimal integer containing only digits `6` and `9`, change at most one `6` to `9` to maximize it.

## Requirements

- `num` contains only decimal digits `6` and `9`.
- Change at most one digit.
- Changing the leftmost `6` gives the maximum result.
- If there is no `6`, return `num` unchanged.

## Source

- Source: LeetCode problem `maximum-69-number`.
- URL: https://leetcode.com/problems/maximum-69-number/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int maximum_69_number(int num) {
    int place = 1;
    int best = 0;
    int temp = num;
    while (temp > 0) {
        int d = temp % 10;
        if (d == 6) best = place;
        place *= 10;
        temp /= 10;
    }
    return num + best * 3;
}
```
