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

```java
class RichestCustomerWealthRows {
    public static int richest_customer_wealth_rows(String accounts) {
        int best = 0;
        for (String row : accounts.split(";")) { int sum = 0; for (String p : row.split(",")) sum += Integer.parseInt(p); if (sum > best) best = sum; }
        return best;
    }
}
```
