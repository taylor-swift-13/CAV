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

```c
int richest_customer_wealth_rows(const char *accounts) {
    int best = 0, sum = 0, i = 0;
    while (1) {
        int v = 0;
        while (accounts[i] >= '0' && accounts[i] <= '9') { v = v * 10 + (accounts[i] - '0'); i++; }
        sum += v;
        if (accounts[i] == ';' || accounts[i] == '\0') { if (sum > best) best = sum; sum = 0; }
        if (accounts[i] == '\0') break;
        i++;
    }
    return best;
}
```
