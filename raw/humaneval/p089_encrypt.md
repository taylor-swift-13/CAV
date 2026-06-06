# P089 Encrypt

## Problem (HumanEval 89)

Create a function p089_encrypt that takes a string as an argument &&
returns a string encrypted with the alphabet being rotated.
The alphabet should be rotated in a manner such that the letters
shift down by two multiplied to two places.
For example:
p089_encrypt("hi") returns "lm"
p089_encrypt("asdfghjkl") returns "ewhjklnop"
p089_encrypt("gf") returns "kj"
p089_encrypt("et") returns "ix"

## Reference Implementation

```c
char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p089_encrypt(char *s)

{
    int i;
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = (s[i] + 4 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
