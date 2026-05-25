# fb_search_max_box_volume

## Problem

Return the largest product `l*b*h` over positive `l` and `b` with `h = s-l-b`.

## Requirements

- `1 <= s <= 100`.
- Use the loops exactly as described.

## Source

- Source: FormalBenchHF base program `MaxVolume.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_max_box_volume(s: i32) -> i32 {
    let mut best = 0;
    for l in 1..=s { for b in 1..=(s - l + 1) { let h = s - l - b; let volume = l * b * h; if volume > best { best = volume; } } }
    best
}
```
