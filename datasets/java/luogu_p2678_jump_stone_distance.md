# Luogu P2678 Jump Stone Distance

## Problem

Return the largest possible minimum jump distance after removing at most `remove` stones.

## Requirements

- `length` is the river length.
- `stones` is a comma-separated sorted list of internal stone positions.

## Source

- Source: Luogu problem `P2678`.
- URL: https://www.luogu.com.cn/problem/P2678
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LuoguP2678JumpStoneDistance {
    public static int luogu_p2678_jump_stone_distance(int length, String stones, int remove) {
        String[] p = stones.split(","); int[] a = new int[p.length + 1]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); a[p.length] = length; int lo = 1, hi = length, ans = 0; while (lo <= hi) { int mid = lo + (hi - lo) / 2, last = 0, removed = 0; for (int x : a) { if (x - last < mid) removed++; else last = x; } if (removed <= remove) { ans = mid; lo = mid + 1; } else hi = mid - 1; } return ans;
    }
}
```
