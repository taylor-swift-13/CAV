# P018 How many times

## Problem (HumanEval 18)

Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> p018_how_many_times("", "a")
0
>>> p018_how_many_times("aaa", "a")
3
>>> p018_how_many_times("aaaa", "aa")
3

## Reference Implementation

```c
/*
Find how many times a given substring can be found in the original string. Count overlaping cases.
>>> p018_how_many_times("", "a")
0
>>> p018_how_many_times("aaa", "a")
3
>>> p018_how_many_times("aaaa", "aa")
3
*/

int strlen(char *s)

;

int p018_how_many_times(char *str, char *substring)

{
    int out = 0;
    int i = 0;
    int j = 0;
    int ok = 0;
    int n0 = strlen(str);
    int m0 = strlen(substring);

    if (n0 == 0) {
        return 0;
    }
    if (m0 == 0) {
        return 0;
    }
    if (m0 > n0) {
        return 0;
    }

    for (i = 0; i <= n0 - m0; i++) {
        ok = 1;

        for (j = 0; j < m0; j++) {
            if (str[i + j] != substring[j]) {
                ok = 0;
            }
        }

        if (ok == 1) {
            out += 1;
        }
    }
    return out;
}
```
