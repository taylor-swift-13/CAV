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

```java
class GoalParserInterpret {
    public static String goal_parser_interpret(String command) {
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < command.length(); ) { if (command.charAt(i) == 'G') { out.append('G'); i++; } else if (command.charAt(i + 1) == ')') { out.append('o'); i += 2; } else { out.append("al"); i += 4; } }
        return out.toString();
    }
}
```
