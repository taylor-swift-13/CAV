# array_min_csv

## Problem

Return the minimum value in nonempty comma-separated integer string `nums`.

## Requirements

- `nums` is nonempty and comma-separated with no spaces.
- Return the smallest integer value.
- Negative numbers are allowed.
- At most 64 integers are encoded.

## Source

- Source: FormalBench-inspired program `array-min`.
- URL: https://github.com/thanhlecongg/FormalBench/
- Data URL: https://huggingface.co/datasets/FormalBench/FormalBench
- License note: this is a local HumanEval-like rewrite for C/Java/Rust shared tests.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ArrayMinCsv {
    public static int array_min_csv(String nums) {
        String[] p = nums.split(",");
        int best = Integer.parseInt(p[0]);
        for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); if (v < best) best = v; }
        return best;
    }
}
```
