# Luogu P2678 Jump Stone Distance

## Problem

Return the largest possible minimum jump distance after removing at most `remove` stones.

## Requirements

- `length` is the river length.
- `stones` is a comma-separated sorted list of internal stone positions.

## Source

- Source: Luogu problem `P2678`.
- URL: https://www.luogu.com.cn/problem/P2678
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p2678_jump_stone_distance(length: i32, stones: &str, remove: i32) -> i32 {
    let mut a: Vec<i32> = stones.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); a.push(length); let mut lo = 1; let mut hi = length; let mut ans = 0; while lo <= hi { let mid = lo + (hi - lo) / 2; let mut last = 0; let mut removed = 0; for &x in &a { if x - last < mid { removed += 1; } else { last = x; } } if removed <= remove { ans = mid; lo = mid + 1; } else { hi = mid - 1; } } ans
}
```
