# richest_customer_wealth_rows

## Problem

Rows of customer accounts are separated by `;`, values in each row by `,`; return the largest row sum.

## Requirements

- Rows are separated by semicolons.
- Values are nonnegative base-10 integers.
- Every row is nonempty.
- Return the maximum row sum.

## Source

- Source: LeetCode problem `richest-customer-wealth`.
- URL: https://leetcode.com/problems/richest-customer-wealth/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn richest_customer_wealth_rows(accounts: &str) -> i32 {
    let mut best = 0;
    for row in accounts.split(';') { let sum: i32 = row.split(',').map(|x| x.parse::<i32>().unwrap()).sum(); if sum > best { best = sum; } }
    best
}
```
