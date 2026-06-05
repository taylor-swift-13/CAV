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

```c
static int lc_eq_find(int p[26], int x) { while (p[x] != x) x = p[x]; return x; }
int lc_equations_possible_bool(const char *equations) {
    int p[26]; for (int i = 0; i < 26; i++) p[i] = i; for (int i = 0; equations[i] != '\0'; ) { int a = equations[i] - 'a', eq = equations[i + 1] == '=', b = equations[i + 3] - 'a'; if (eq) p[lc_eq_find(p, a)] = lc_eq_find(p, b); i += 4; if (equations[i] == ';') i++; } for (int i = 0; equations[i] != '\0'; ) { int a = equations[i] - 'a', neq = equations[i + 1] == '!', b = equations[i + 3] - 'a'; if (neq && lc_eq_find(p, a) == lc_eq_find(p, b)) return 0; i += 4; if (equations[i] == ';') i++; } return 1;
}
```
