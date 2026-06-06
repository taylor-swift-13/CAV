# P054 Same chars

## Problem (HumanEval 54)

Check if two words have the same characters.
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> p054_same_chars("abcd", "dddddddabc")
true
>>> p054_same_chars("dddddddabc", "abcd")
true
>>> p054_same_chars("eabcd", "dddddddabc")
false
>>> p054_same_chars("abcd", "dddddddabce")
false
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false

## Reference Implementation

```c
/*
Check if two words have the same characters.
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddeddabc")
true
>>> p054_same_chars("abcd", "dddddddabc")
true
>>> p054_same_chars("dddddddabc", "abcd")
true
>>> p054_same_chars("eabcd", "dddddddabc")
false
>>> p054_same_chars("abcd", "dddddddabce")
false
>>> p054_same_chars("eabcdzzzz", "dddzzzzzzzddddabc")
false
*/

int strlen(char *s)

;

char *strchr(char *s, int c)

;

int p054_same_chars(char *s0, char *s1)

{
    int len0 = strlen(s0);
    int len1 = strlen(s1);
    int i;

    for (i = 0; i < len0; i++)
    {
        int chr = s0[i];
        char *found = strchr(s1, chr);
        if (found == 0) {
            return 0;
        }
    }

    for (i = 0; i < len1; i++)
    {
        int chr = s1[i];
        char *found = strchr(s0, chr);
        if (found == 0) {
            return 0;
        }
    }
    return 1;
}
```
