# P038 Decode cyclic

## Problem (HumanEval 38)



## Reference Implementation

```c
/*
p038_decode_cyclic takes as input a string encoded with encode_cyclic and returns
the decoded string. Only p038_decode_cyclic is verified for problem 38.
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p038_decode_cyclic(char *s)

{
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);
    int full = (n / 3) * 3;
    int i;

    for (i = 0; i < n; i++) {
        if (i < full) {
            if ((i + 1) % 3 == 1) {

                out[i] = s[i + 2];
            } else {

                out[i] = s[i - 1];
            }
        } else {

            out[i] = s[i];
        }
    }
    out[n] = 0;
    return out;
}
```
