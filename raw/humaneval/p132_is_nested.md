# P132 Is nested

## Problem (HumanEval 132)

Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

p132_is_nested("[[]]") ➞ true
p132_is_nested("[]]]]]]][[[[[]") ➞ false
p132_is_nested("[][]") ➞ false
p132_is_nested("[]") ➞ false
p132_is_nested("[[][]]") ➞ true
p132_is_nested("[[]][[") ➞ true

## Reference Implementation

```c
/*
Create a function that takes a string as input which contains only square brackets.
The function should return true if && only if there is a valid subsequence of brackets
where at least one bracket in the subsequence is nested.

p132_is_nested("[[]]") -> true
p132_is_nested("[]]]]]]][[[[[]") -> false
p132_is_nested("[][]") -> false
p132_is_nested("[]") -> false
p132_is_nested("[[][]]") -> true
p132_is_nested("[[]][[") -> true
*/

int strlen(char *s)

;

int p132_is_nested(char *str)

{
    int state = 0;
    int i;
    int n = strlen(str);

    for (i = 0; i < n; i++) {
        int chr = str[i];
        if (state == 0) {
            if (chr == 91) {
                state = 1;
            }
        } else if (state == 1) {
            if (chr == 91) {
                state = 2;
            }
        } else if (state == 2) {
            if (chr == 93) {
                state = 3;
            }
        } else if (state == 3) {
            if (chr == 93) {
                state = 4;
            }
        }
    }
    if (state == 4) {
        return 1;
    }
    return 0;
}
```
