# subtract_product_and_sum_digits

## Problem

Return the product of decimal digits of `n` minus the sum of those digits.

## Requirements

- `n > 0`.
- Use the ordinary base-10 digits of `n`.
- Compute product and sum over all digits.
- Return product minus sum.

## Source

- Source: LeetCode problem `subtract-the-product-and-sum-of-digits-of-an-integer`.
- URL: https://leetcode.com/problems/subtract-the-product-and-sum-of-digits-of-an-integer/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int subtract_product_and_sum_digits(int n) {
    int product = 1;
    int sum = 0;
    while (n > 0) {
        int d = n % 10;
        product *= d;
        sum += d;
        n /= 10;
    }
    return product - sum;
}
```
