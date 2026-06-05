# goal_parser_interpret

## Problem

Interpret a command string where `G` maps to `G`, `()` maps to `o`, and `(al)` maps to `al`.

## Requirements

- Input is a concatenation of tokens `G`, `()`, and `(al)`.
- Map tokens exactly as specified.
- Return the concatenated interpreted string.
- No other characters appear.

## Source

- Source: LeetCode problem `goal-parser-interpretation`.
- URL: https://leetcode.com/problems/goal-parser-interpretation/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
#include <stdlib.h>
char *goal_parser_interpret(const char *command) {
    int n = 0;
    while (command[n] != '\0') n++;
    char *out = (char *)malloc((unsigned long)n + 1);
    int pos = 0;
    for (int i = 0; command[i] != '\0'; ) {
        if (command[i] == 'G') { out[pos++] = 'G'; i++; }
        else if (command[i + 1] == ')') { out[pos++] = 'o'; i += 2; }
        else { out[pos++] = 'a'; out[pos++] = 'l'; i += 4; }
    }
    out[pos] = '\0';
    return out;
}
```
