# Luogu P5729 Remaining Cubes

## Problem

Return how many unit cubes remain after deleting inclusive cuboids from a `w*x*h` block.

## Requirements

- Cuboids are encoded as `x1,y1,z1,x2,y2,z2;...` using one-based inclusive coordinates.
- The empty cuboid string deletes nothing.
- `w`, `x`, and `h` are at most 20 in supplied tests.

## Source

- Source: Luogu problem `P5729`.
- URL: https://www.luogu.com.cn/problem/P5729
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5729_remaining_cubes(w: i32, x: i32, h: i32, cuts: &str) -> i32 {
    let mut used = vec![vec![vec![false; (h + 1) as usize]; (x + 1) as usize]; (w + 1) as usize]; if !cuts.is_empty() { for cut in cuts.split(';') { let v: Vec<usize> = cut.split(',').map(|p| p.parse::<usize>().unwrap()).collect(); let mut a = v[0]; while a <= v[3] { let mut b = v[1]; while b <= v[4] { let mut c = v[2]; while c <= v[5] { used[a][b][c] = true; c += 1; } b += 1; } a += 1; } } }
    let mut left = 0; let mut a = 1usize; while a <= w as usize { let mut b = 1usize; while b <= x as usize { let mut c = 1usize; while c <= h as usize { if !used[a][b][c] { left += 1; } c += 1; } b += 1; } a += 1; } left
}
```
