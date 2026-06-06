# P011 String xor

## Problem (HumanEval 11)

Input are two strings a && b consisting only of 1s && 0s.
Perform binary XOR on these inputs && return result also as a string.
>>> p011_string_xor("010", "110")
"100"

## Reference Implementation

```c
char *malloc_char_array(int n)

;

int strlen(char *s)

;

char *p011_string_xor(char *a, char *b)

{
    int i;
    int n1 = strlen(a);
    int n2 = strlen(b);
    int n;
    if (n1 < n2) {
        n = n1;
    } else {
        n = n2;
    }



    char *output = malloc_char_array(n + 1);

    for (i = 0; i < n; i++) {
        if (a[i] == b[i]) {
            output[i] = 48;
        } else {
            output[i] = 49;
        }
    }
    output[n] = 0;
    return output;
}
```
