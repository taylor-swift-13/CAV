# P098 Count upper

## Problem (HumanEval 98)

Given a string s, count the number of uppercase vowels in even indices.

For example:
p098_count_upper("aBCdEf") returns 1
p098_count_upper("abcdefg") returns 0
p098_count_upper("dBBE") returns 0

## Reference Implementation

```c
/*
Given a string s, count the number of uppercase vowels in even indices.

For example:
p098_count_upper("aBCdEf") returns 1
p098_count_upper("abcdefg") returns 0
p098_count_upper("dBBE") returns 0
*/

int strlen(char *s)

;

int p098_count_upper(char *s)

{
    int n = strlen(s);
    int count = 0;
    int i;

    for (i = 0; i < n; i++) {
        if (i % 2 == 0) {
            if (s[i] == 65 || s[i] == 69 || s[i] == 73 ||
                s[i] == 79 || s[i] == 85) {
                count = count + 1;
            }
        }
    }
    return count;
}
```
