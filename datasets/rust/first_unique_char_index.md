# first_unique_char_index

## Problem

Return the index of the first non-repeating lowercase letter in `s`, or `-1` if none exists.

## Requirements

- `s` contains only lowercase English letters.
- Return a zero-based index.
- If all characters repeat, return `-1`.
- The empty string is outside this task.

## Source

- Source: LeetCode problem `first-unique-character-in-a-string`.
- URL: https://leetcode.com/problems/first-unique-character-in-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn first_unique_char_index(s: &str) -> i32 {
    let mut count = [0i32; 26];
    for b in s.bytes() { count[(b - b'a') as usize] += 1; }
    let mut i = 0;
    for b in s.bytes() { if count[(b - b'a') as usize] == 1 { return i; } i += 1; }
    -1
}
```
