# integer_sqrt_floor

## Problem

Return the greatest integer `r` such that `r * r <= x`.

## Requirements

- `x` is a nonnegative signed 32-bit integer.
- Return the floor of the real square root, not a rounded value.
- Do not use floating point arithmetic, exponentiation, or a library square-root routine.
- The implementation must avoid overflow when comparing `mid * mid` with `x`.

## Source

- Source: LeetCode problem `sqrtx`.
- URL: https://leetcode.com/problems/sqrtx/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn integer_sqrt_floor(x: i32) -> i32 {
    let mut lo = 0;
    let mut hi = 46340;
    let mut ans = 0;
    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        if mid == 0 || mid <= x / mid { ans = mid; lo = mid + 1; }
        else { hi = mid - 1; }
    }
    ans
}
```
