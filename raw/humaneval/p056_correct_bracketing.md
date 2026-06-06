# P056 Correct bracketing

## Problem (HumanEval 56)

brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> p056_correct_bracketing("<")
false
>>> p056_correct_bracketing("<>")
true
>>> p056_correct_bracketing("<<><>>")
true
>>> p056_correct_bracketing("><<>")
false

## Reference Implementation

```c
/*
brackets is a string of '<' && '>'.
return true if every opening bracket has a corresponding closing bracket.

>>> p056_correct_bracketing("<")
false
>>> p056_correct_bracketing("<>")
true
>>> p056_correct_bracketing("<<><>>")
true
>>> p056_correct_bracketing("><<>")
false
*/

int strlen(char *s)

;

int p056_correct_bracketing(char *brackets)

{
    int level = 0;
    int n = strlen(brackets);
    int i;

    for (i = 0; i < n; i++) {
        if (brackets[i] == 60) {
            level = level + 1;
        } else if (brackets[i] == 62) {
            level = level - 1;
        }
        if (level < 0) {
            return 0;
        }
    }
    if (level != 0) {
        return 0;
    }
    return 1;
}
```
