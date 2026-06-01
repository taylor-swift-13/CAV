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

```java
class SgMatrix2x2ProductTrace {
    public static int sg_matrix_2x2_product_trace(int a00, int a01, int a10, int a11, int b00, int b01, int b10, int b11) {
        int c00 = a00 * b00 + a01 * b10;
        int c11 = a10 * b01 + a11 * b11;
        return c00 + c11;
    }
}
```
