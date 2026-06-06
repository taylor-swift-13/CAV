# P061 Correct bracketing

## Problem (HumanEval 61)

brackets is a string of '(' && ')'.
return true if every opening bracket has a corresponding closing bracket.

>>> p061_correct_bracketing("(")
false
>>> p061_correct_bracketing("()")
true
>>> p061_correct_bracketing("(()())")
true
>>> p061_correct_bracketing(")(()")
false

## Reference Implementation

```c
/*
brackets is a string of '(' && ')'.
return true if every opening bracket has a corresponding closing bracket.

>>> p061_correct_bracketing("(")
false
>>> p061_correct_bracketing("()")
true
>>> p061_correct_bracketing("(()())")
true
>>> p061_correct_bracketing(")(()")
false
*/

int strlen(char *s)

;

int p061_correct_bracketing(char *brackets)

{
    int level = 0;
    int n = strlen(brackets);
    int i;

    for (i = 0; i < n; i++) {
        if (brackets[i] == 40) {
            level = level + 1;
        } else if (brackets[i] == 41) {
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
