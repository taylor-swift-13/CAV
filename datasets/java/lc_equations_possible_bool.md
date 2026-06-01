# LC Equality Equations Possible Bool

## Problem

Return true if all equality and inequality equations can be satisfied.

## Requirements

- Equations are separated by semicolons, e.g. `a==b;b!=c`.
- Variables are lowercase English letters.

## Source

- Source: LeetCode problem `satisfiability-of-equality-equations`.
- URL: https://leetcode.com/problems/satisfiability-of-equality-equations/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcEquationsPossibleBool {
    static int find(int[] p, int x) { while (p[x] != x) x = p[x]; return x; }
    public static boolean lc_equations_possible_bool(String equations) {
        int[] p = new int[26]; for (int i = 0; i < 26; i++) p[i] = i; for (String e : equations.split(";")) if (e.charAt(1) == '=') p[find(p, e.charAt(0) - 'a')] = find(p, e.charAt(3) - 'a'); for (String e : equations.split(";")) if (e.charAt(1) == '!' && find(p, e.charAt(0) - 'a') == find(p, e.charAt(3) - 'a')) return false; return true;
    }
}
```
