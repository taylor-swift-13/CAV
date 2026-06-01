# LC Teemo Attacking Duration CSV

## Problem

Return total poisoned duration from attack times and a fixed duration.

## Requirements

- `times` is a nonempty sorted comma-separated list of attack times.
- `duration > 0`.

## Source

- Source: LeetCode problem `teemo-attacking`.
- URL: https://leetcode.com/problems/teemo-attacking/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcTeemoAttackingDurationCsv {
    public static int lc_teemo_attacking_duration_csv(String times, int duration) {
        String[] p = times.split(","); int ans = duration, prev = Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int v = Integer.parseInt(p[i]); ans += Math.min(duration, v - prev); prev = v; } return ans;
    }
}
```
