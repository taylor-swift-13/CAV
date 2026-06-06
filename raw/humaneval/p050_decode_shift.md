# P050 Decode shift

## Problem (HumanEval 50)



## Reference Implementation

```c
char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *encode_shift(char *s)

{
    int i;
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = (s[i] + 5 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}

char *p050_decode_shift(char *s)

{
    int i;
    int n = strlen(s);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = (s[i] + 21 - 97) % 26 + 97;
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
