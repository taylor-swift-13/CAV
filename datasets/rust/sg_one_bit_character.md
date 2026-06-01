# SpecGenBench One Bit Character

## Problem

Decode a bit array where `0` is a one-bit character and `10`/`11` are two-bit characters; return true if the last character is one-bit.

## Requirements

- `n > 0` and `bits` has at least `n` elements.
- Each bit is `0` or `1`.
- The last bit is `0`.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/IsOneBitCharacter`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/IsOneBitCharacter/IsOneBitCharacter.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_one_bit_character(n: i32, bits: &[i32]) -> bool {
    let mut i = 0;
    while i < n - 1 { i += bits[i as usize] + 1; }
    i == n - 1
}
```
