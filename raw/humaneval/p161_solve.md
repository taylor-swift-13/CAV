# P161 Solve

## Problem (HumanEval 161)

You are given a string s.
if s[i] is a letter, reverse its case from lower to upper || vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
The function should return the resulted string.
Examples
p161_solve("1234") = "4321"
p161_solve("ab") = "AB"
p161_solve("#a@C") = "#A@c"

## Reference Implementation

```c
/*
Given a string s.
if s[i] is a letter, reverse its case from lower to upper or vise versa,
otherwise keep it as it is.
If the string contains no letters, reverse the string.
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p161_solve(char *s)

{
    int i;
    int n = strlen(s);
    int has_letter = 0;
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = s[i];
        if ((w >= 65 && w <= 90) || (w >= 97 && w <= 122)) {
            has_letter = 1;
        }
    }

    if (has_letter == 1) {

        for (i = 0; i < n; i++) {
            int w = s[i];
            if (w >= 65 && w <= 90) {
                w = w + 32;
            } else if (w >= 97 && w <= 122) {
                w = w - 32;
            }
            out[i] = w;
        }
    } else {

        for (i = 0; i < n; i++) {
            out[i] = s[n - 1 - i];
        }
    }
    out[n] = 0;
    return out;
}
```
