# add_digits

## Problem

Repeatedly sum the decimal digits of `num` until only one digit remains, then return it.

## Requirements

- `num` is a nonnegative signed 32-bit integer.
- If `num` is already a single decimal digit, return it unchanged.
- The repeated-sum process must continue until the result is in `[0, 9]`.
- This local reference uses the direct iterative process rather than the digital-root formula.

## Source

- Source: LeetCode problem `add-digits`.
- URL: https://leetcode.com/problems/add-digits/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int add_digits(int num) {
    while (num >= 10) {
        int sum = 0;
        while (num > 0) { sum += num % 10; num /= 10; }
        num = sum;
    }
    return num;
}
```
