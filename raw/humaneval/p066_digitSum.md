# P066 DigitSum

## Problem (HumanEval 66)

Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    p066_digitSum("") => 0
    p066_digitSum("abAB") => 131
    p066_digitSum("abcCd") => 67
    p066_digitSum("helloE") => 69
    p066_digitSum("woArBld") => 131
    p066_digitSum("aAaaaXa") => 153

## Reference Implementation

```c
/*
Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    p066_digitSum("") => 0
    p066_digitSum("abAB") => 131
    p066_digitSum("abcCd") => 67
    p066_digitSum("helloE") => 69
    p066_digitSum("woArBld") => 131
    p066_digitSum("aAaaaXa") => 153
*/

int strlen(char *s)

;

int p066_digitSum(char *s)

{
    int sum = 0;
    int n = strlen(s);
    int i;

    for (i = 0; i < n; i++) {
        if (s[i] >= 65 && s[i] <= 90) {
            sum = sum + s[i];
        }
    }
    return sum;
}
```
