# Exercism Scrabble Score

## Problem

Return the Scrabble score of an ASCII word.

## Requirements

- Letters are scored case-insensitively.
- Nonletters score zero.

## Source

- Source: Exercism problem `scrabble-score`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/scrabble-score
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_scrabble_score(word: &str) -> i32 {
    let score = [1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10]; let mut ans = 0; for mut ch in word.bytes() { if ch >= b'A' && ch <= b'Z' { ch = ch - b'A' + b'a'; } if ch >= b'a' && ch <= b'z' { ans += score[(ch - b'a') as usize]; } } ans
}
```
