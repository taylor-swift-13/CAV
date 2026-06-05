# LC Robot Return To Origin Bool

## Problem

Return true if robot moves return to coordinate `(0,0)`.

## Requirements

- `moves` contains only `U`, `D`, `L`, and `R`.

## Source

- Source: LeetCode problem `robot-return-to-origin`.
- URL: https://leetcode.com/problems/robot-return-to-origin/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_robot_return_origin_bool(const char *moves) {
    int x = 0, y = 0; for (int i = 0; moves[i] != '\0'; i++) { if (moves[i] == 'U') y++; else if (moves[i] == 'D') y--; else if (moves[i] == 'L') x--; else if (moves[i] == 'R') x++; } return x == 0 && y == 0;
}
```
