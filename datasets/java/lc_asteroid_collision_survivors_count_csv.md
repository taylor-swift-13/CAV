# LC Asteroid Collision Survivors Count CSV

## Problem

Simulate asteroid collisions and return the number of surviving asteroids.

## Requirements

- `asteroids` is a comma-separated list of nonzero integers.
- Positive moves right and negative moves left.

## Source

- Source: LeetCode problem `asteroid-collision`.
- URL: https://leetcode.com/problems/asteroid-collision/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcAsteroidCollisionSurvivorsCountCsv {
    public static int lc_asteroid_collision_survivors_count_csv(String asteroids) {
        int[] st = new int[256]; int top = 0; for (String part : asteroids.split(",")) { int v = Integer.parseInt(part); boolean alive = true; while (alive && v < 0 && top > 0 && st[top - 1] > 0) { if (st[top - 1] < -v) top--; else if (st[top - 1] == -v) { top--; alive = false; } else alive = false; } if (alive) st[top++] = v; } return top;
    }
}
```
