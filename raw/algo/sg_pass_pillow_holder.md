# SpecGenBench Pass Pillow Holder

## Problem

Return who holds a pillow after `time` seconds when it moves from person `1` to `n` and then reverses direction repeatedly.

## Requirements

- `n >= 2`.
- `time >= 0`.
- The pillow moves one position per second.

## Source

- Source: SpecGenBench problem `SpecGenBench/common/PassPillow`.
- URL: file:///home/yangfp/Arc/represent/external/specgen-artifact/benchmark/SpecGenBench/common/PassPillow/PassPillow.java
- License note: local three-language rewrite from local external benchmark.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int sg_pass_pillow_holder(int n, int time) {
    int period = (n - 1) * 2;
    time %= period;
    if (time < n) return time + 1;
    return n * 2 - time - 1;
}
```
