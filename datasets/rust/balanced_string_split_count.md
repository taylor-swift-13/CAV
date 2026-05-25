# balanced_string_split_count

## Problem

Return the maximum number of balanced substrings in a string containing only `L` and `R`.

## Requirements

- Input contains only `L` and `R`.
- The full input is balanced.
- A balanced substring has the same number of `L` and `R` characters.
- Return the maximum count obtained by greedy left-to-right splitting.

## Source

- Source: LeetCode problem `split-a-string-in-balanced-strings`.
- URL: https://leetcode.com/problems/split-a-string-in-balanced-strings/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn balanced_string_split_count(s: &str) -> i32 {
    let mut balance = 0; let mut count = 0;
    for b in s.bytes() { if b == b'L' { balance += 1; } else { balance -= 1; } if balance == 0 { count += 1; } }
    count
}
```
