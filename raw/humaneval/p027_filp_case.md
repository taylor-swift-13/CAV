# P027 Filp case

## Problem (HumanEval 27)

For a given string, flip lowercase characters to uppercase && uppercase to lowercase.
>>> flip_case("Hello")
"hELLO"

## Reference Implementation

```c
/*
For a given string, flip lowercase characters to uppercase && uppercase to lowercase.
>>> flip_case("Hello")
"hELLO"
*/

char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p027_filp_case(char *str)

{
    int i;
    int n = strlen(str);
    char *out = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        int w = str[i];
        if (w >= 97 && w <= 122) {
            w = w - 32;
        } else if (w >= 65 && w <= 90) {
            w = w + 32;
        }
        out[i] = w;
    }
    out[n] = 0;
    return out;
}
```
