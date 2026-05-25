# fb_search_lateral_surface_special

## Problem

Return the recorded lateral surface area for cube side lengths `5`, `9`, and `10`; return `-1` for other lengths.

## Requirements

- `0 <= l <= 100`.
- Use the exact recorded branch behavior.

## Source

- Source: FormalBenchHF base program `LateralsurfaceCube.java` from SESpec `represent/bench/java_flat`.
- URL: https://github.com/thanhlecongg/FormalBench/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn fb_search_lateral_surface_special(l: i32) -> i32 {
    if l == 5 { 100 } else if l == 9 { 324 } else if l == 10 { 400 } else { -1 }
}
```
