# LC Decode Ways Count

## Problem

Return how many ways digit string `s` can be decoded with `1 -> A` through `26 -> Z`.

## Requirements

- `s` contains digits only.
- The empty string returns `0`.
- The result fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `decode-ways`.
- URL: https://leetcode.com/problems/decode-ways/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_decode_ways_count(s: &str) -> i32 {
    let b = s.as_bytes();
    let n = b.len();
    if n == 0 { return 0; }
    let mut dp = [0i32; 128];
    dp[0] = 1;
    dp[1] = if b[0] == b'0' { 0 } else { 1 };
    let mut i = 2usize;
    while i <= n { if b[i - 1] != b'0' { dp[i] += dp[i - 1]; } let two = ((b[i - 2] - b'0') as i32) * 10 + (b[i - 1] - b'0') as i32; if two >= 10 && two <= 26 { dp[i] += dp[i - 2]; } i += 1; }
    dp[n]
}
```
