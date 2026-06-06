# P023 Strlen

## Problem (HumanEval 23)

Return length of given string
>>> p023_strlen("")
0
>>> p023_strlen("abc")
3

## Reference Implementation

```c
/*
Return length of given string
>>> p023_strlen("")
0
>>> p023_strlen("abc")
3
*/

int p023_strlen(char *str)

{
    int i = 0;

    while (1) {
        if (str[i] == 0) {
            break;
        }
        i++;
    }

    return i;
}
```
