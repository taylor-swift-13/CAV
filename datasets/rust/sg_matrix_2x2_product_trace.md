# SpecGenBench Matrix 2x2 Product Trace

## Problem

Return the trace of the product of two 2x2 matrices `A` and `B`.

## Requirements

- Inputs are provided row-major as eight integers.
- Intermediate products and the final sum fit in signed 32-bit integer range.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/MatrixMul`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/MatrixMul/MatrixMul.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn sg_matrix_2x2_product_trace(a00: i32, a01: i32, a10: i32, a11: i32, b00: i32, b01: i32, b10: i32, b11: i32) -> i32 {
    let c00 = a00 * b00 + a01 * b10;
    let c11 = a10 * b01 + a11 * b11;
    c00 + c11
}
```
