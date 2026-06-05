# Digitsum 66

## Problem (HumanEval 66)

Task
Write a function that takes a string as input && returns the sum of the upper characters only's
ASCII codes.

Examples:
    digitSum_66("") => 0
    digitSum_66("abAB") => 131
    digitSum_66("abcCd") => 67
    digitSum_66("helloE") => 69
    digitSum_66("woArBld") => 131
    digitSum_66("aAaaaXa") => 153

## Reference Implementation

```c
int digitSum_66(const char* s){
    int sum=0;
    for (size_t i=0;i<strlen(s);i++)
        if (s[i]>=65 && s[i]<=90)
            sum+=s[i];
    return sum;
}
```
