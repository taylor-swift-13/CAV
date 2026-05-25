# fb_search_rectangle_count

## Problem

Count positive integer side pairs `(a,b)` whose rectangle diagonal fits inside a circle with the given `radius`.

## Requirements

- `1 <= radius <= 20`.
- Use inclusive loops over side lengths from `1` to `2*radius`.

## Source

- Source: FormalBenchHF base program `CountRectangles.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_rectangle_count(radius: i32) -> i32 {
    let (mut count, limit) = (0, 2 * radius); let d2 = limit * limit;
    for a in 1..=limit { for b in 1..=limit { if a * a + b * b <= d2 { count += 1; } } }
    count
}
```
