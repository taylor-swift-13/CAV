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

```c
int lc_asteroid_collision_survivors_count_csv(const char *asteroids) {
    int st[256], top = 0, i = 0; while (asteroids[i] != '\0') { int sign = 1, v = 0; if (asteroids[i] == '-') { sign = -1; i++; } while (asteroids[i] >= '0' && asteroids[i] <= '9') { v = v * 10 + asteroids[i] - '0'; i++; } v *= sign; int alive = 1; while (alive && v < 0 && top > 0 && st[top - 1] > 0) { if (st[top - 1] < -v) top--; else if (st[top - 1] == -v) { top--; alive = 0; } else alive = 0; } if (alive) st[top++] = v; if (asteroids[i] == ',') i++; } return top;
}
```
