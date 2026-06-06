# P015 String sequence

## Problem (HumanEval 15)

Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> p015_string_sequence(0)
"0"
>>> p015_string_sequence(5)
"0 1 2 3 4 5"

## Reference Implementation

```c
/*
Return a string containing space-delimited numbers starting from 0 upto n inclusive.
>>> p015_string_sequence(0)
"0"
>>> p015_string_sequence(5)
"0 1 2 3 4 5"
*/

char *malloc_char_array(int n)

;

char* p015_string_sequence(int n)

{
    int cap = 12 * (n + 1) + 1;
    char *out = malloc_char_array(cap);
    int k = 0;
    int i = 1;

    out[0] = 48;
    k = 1;

    {
    int t = 0;
    int digits = 0;
    int j = 0;
    int fill = 0;

    for (i = 1; i <= n; i++) {
        t = i;
        digits = 0;

        while (t > 0) {
            digits = digits + 1;
            t = t / 10;
        }

        out[k] = 32;
        k = k + 1;

        for (j = 0; j < digits; j++) {
            out[k + j] = 0;
        }

        t = i;
        fill = digits;

        while (t > 0) {
            fill = fill - 1;

            out[k + fill] = 48 + (t % 10);
            t = t / 10;
        }

        k = k + digits;
    }
    }

    out[k] = 0;

    return out;
}
```
