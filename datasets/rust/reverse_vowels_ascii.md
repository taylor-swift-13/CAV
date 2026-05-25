# reverse_vowels_ascii

## Problem

Return a copy of `s` with only ASCII vowels reversed.

## Requirements

- `s` contains only ASCII characters in this dataset variant.
- Vowels are `a e i o u` and `A E I O U`.
- Only vowel positions change; consonants, digits, punctuation, and spaces remain at their original positions.
- The relative order of reversed vowels follows a full two-pointer reversal.

## Source

- Source: LeetCode problem `reverse-vowels-of-a-string`.
- URL: https://leetcode.com/problems/reverse-vowels-of-a-string/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
fn is_vowel_rv(c: u8) -> bool { b"aeiouAEIOU".contains(&c) }
pub fn reverse_vowels_ascii(s: &str) -> String {
    let mut out = s.as_bytes().to_vec();
    if out.is_empty() { return String::new(); }
    let mut l: usize = 0;
    let mut r: usize = out.len() - 1;
    while l < r {
        while l < r && !is_vowel_rv(out[l]) { l += 1; }
        while l < r && !is_vowel_rv(out[r]) { r -= 1; }
        if l < r { out.swap(l, r); l += 1; r -= 1; }
    }
    String::from_utf8(out).unwrap()
}
```
