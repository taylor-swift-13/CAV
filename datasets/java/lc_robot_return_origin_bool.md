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

```java
class LcRobotReturnOriginBool {
    public static boolean lc_robot_return_origin_bool(String moves) {
        int x = 0, y = 0; for (int i = 0; i < moves.length(); i++) { char ch = moves.charAt(i); if (ch == 'U') y++; else if (ch == 'D') y--; else if (ch == 'L') x--; else if (ch == 'R') x++; } return x == 0 && y == 0;
    }
}
```
