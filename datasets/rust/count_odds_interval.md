# count_odds_interval

## Problem

Return how many odd integers lie in the inclusive interval `[low, high]`.

## Requirements

- `low <= high`.
- Both interval endpoints are included.
- Negative values are outside this simplified task.
- Return the count, not the odd values.

## Source

- Source: LeetCode problem `count-odd-numbers-in-an-interval-range`.
- URL: https://leetcode.com/problems/count-odd-numbers-in-an-interval-range/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn count_odds_interval(low: i32, high: i32) -> i32 {
    let mut count = 0;
    let mut x = low;
    while x <= high { if x % 2 != 0 { count += 1; } x += 1; }
    count
}
```
