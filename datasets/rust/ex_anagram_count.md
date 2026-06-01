# Exercism Anagram Count

## Problem

Count candidate words that are anagrams of `subject` but not equal to it ignoring case.

## Requirements

- Candidates are separated by semicolons.
- Inputs are ASCII alphabetic words.

## Source

- Source: Exercism problem `anagram`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/anagram
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn ex_anagram_count(subject: &str, candidates: &str) -> i32 {
    fn counts(s: &str) -> [i32; 26] { let mut c = [0; 26]; for mut ch in s.bytes() { if ch >= b'A' && ch <= b'Z' { ch = ch - b'A' + b'a'; } c[(ch - b'a') as usize] += 1; } c }
    let base = counts(subject); let lower = subject.to_ascii_lowercase(); let mut ans = 0; for cand in candidates.split(';') { if cand.to_ascii_lowercase() == lower { continue; } if counts(cand) == base { ans += 1; } } ans
}
```
