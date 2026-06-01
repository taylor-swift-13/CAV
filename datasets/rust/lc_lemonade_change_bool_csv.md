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

```rust
pub fn lc_lemonade_change_bool_csv(bills: &str) -> bool {
    let mut five = 0; let mut ten = 0; for part in bills.split(',') { let v = part.parse::<i32>().unwrap(); if v == 5 { five += 1; } else if v == 10 { if five == 0 { return false; } five -= 1; ten += 1; } else if ten > 0 && five > 0 { ten -= 1; five -= 1; } else if five >= 3 { five -= 3; } else { return false; } } true
}
```
