# sentence_is_pangram_ascii

## Problem

Return true if lowercase sentence `sentence` contains every English letter at least once.

## Requirements

- Input contains only lowercase English letters.
- Return true exactly when all 26 letters appear.
- Repeated letters are allowed.
- The empty string is not pangram.

## Source

- Source: LeetCode problem `check-if-the-sentence-is-pangram`.
- URL: https://leetcode.com/problems/check-if-the-sentence-is-pangram/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sentence_is_pangram_ascii(sentence: &str) -> bool {
    let mut seen = [false; 26]; let mut count = 0;
    for b in sentence.bytes() { let k = (b - b'a') as usize; if !seen[k] { seen[k] = true; count += 1; } }
    count == 26
}
```
