# LC Keys And Rooms Bool

## Problem

Return true if every room can be visited starting from room `0`.

## Requirements

- Rooms are semicolon-separated.
- Keys inside a room are comma-separated room numbers; `-` encodes no keys.

## Source

- Source: LeetCode problem `keys-and-rooms`.
- URL: https://leetcode.com/problems/keys-and-rooms/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcKeysAndRoomsBool {
    public static boolean lc_keys_and_rooms_bool(String rooms) {
        String[] rs = rooms.split(";"); boolean[] seen = new boolean[rs.length]; int[] stack = new int[rs.length]; int top = 0, count = 0; stack[top++] = 0; seen[0] = true; while (top > 0) { int v = stack[--top]; count++; if (!rs[v].equals("-")) for (String p : rs[v].split(",")) { int key = Integer.parseInt(p); if (!seen[key]) { seen[key] = true; stack[top++] = key; } } } return count == rs.length;
    }
}
```
