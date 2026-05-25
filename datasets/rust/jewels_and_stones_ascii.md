# jewels_and_stones_ascii

## Problem

Return how many characters in `stones` are also present in `jewels`.

## Requirements

- Inputs are ASCII strings.
- `jewels` characters are distinct in the original task, but this implementation also handles duplicates.
- Count every stone whose character appears in `jewels`.
- Case is significant.

## Source

- Source: LeetCode problem `jewels-and-stones`.
- URL: https://leetcode.com/problems/jewels-and-stones/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn jewels_and_stones_ascii(jewels: &str, stones: &str) -> i32 {
    let jb = jewels.as_bytes(); let mut count = 0;
    for s in stones.bytes() { if jb.contains(&s) { count += 1; } }
    count
}
```
